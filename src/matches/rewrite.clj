(ns matches.rewrite
  "This namespace defines several rulesets and related macros that enhance the expressive
  power of the rules engine.

  Most of these rulesets are defined in a style inspired by the nanopass compiler, using
  directed to control the rule matcher's descent into the expression
  being transformed.

  The rules defined in this namespace must make use of a limited subset of this library's
  functionality since they are defining that functionality in terms of the base operations.

  Arity-1 rules may not be used, nor may sub or quo.

  This namespace defines several functions in terms of various combinations of the same
  rulesets. The core idea is to transform native Clojure sytax-quoted forms. In the case
  of regular quoted lists, they may be expanded into syntax-quoted form before being transformed
  and then possibly simplified back as close to their original shape as possible. This
  transformation enables unquoting on regular quoted lists and other data structures.

  Note that `sequence` is included in the rules because when booting, Clojure's
  syntax quote expands slightly differently than at runtime. It also uses lists rather
  than Cons objects at boot."
  (:require [matches.match.core :refer [matcher-type-for-dispatch var-name]]
            [matches.rules :as r :refer [rule success rule-name pattern-args]]
            [clojure.walk :as walk]
            [matches.rule-combinators :refer [descend
                                              rule-list in-order rule-simplifier
                                              iterated-on-subexpressions
                                              on-subexpressions
                                              directed]]))

(def remove-expressions
  "Replace all unquoted expressions with 'identity but leave the structure of the
  expression unmodified."
  (rule-name :remove-expressions
             (directed
              (rule-list [(rule `(seq ?->s)
                                `(seq ~s))
                          (rule `(sequence ?->s)
                                `(sequence ~s))
                          (rule `(list ?->item)
                                `(list ~item))
                          (rule `(concat ??->lists)
                                `(concat ~@lists))
                          (rule `(apply hash-set ?->v)
                                `(apply hash-set ~v))
                          (rule `(apply hash-map ?->v)
                                ;; Don't return a map because keys won't stay unique in
                                ;; the next stage, which would cause values to be lost.
                                `(apply vector ~v))
                          (rule `(apply vector ?->v)
                                `(apply vector ~v))
                          (rule '(quote ?quoted)
                                `(~'quote ~quoted))
                          (rule '?other '(quote identity))]))))

(def evaluate-structure
  "Evaluate syntax quoted forms "
  ;; The result will run through `sub` and would match, but by using
  ;; `success` to wrap the result, it should not get any substitutions done:
  (rule-name :evaluate-structure
             (directed
              (rule-list [(rule `(seq ?->s) (success s))
                          (rule `(sequence ?->s) (success s))
                          (rule `(list ?->item) (list item))
                          (rule `(concat ??->lists) (apply concat lists))
                          (rule `(apply hash-set ?->v) (set v))
                          (rule `(apply vector ?->v) (vec v))
                          (rule '(quote ?quoted) (success quoted))]))))

(def pure-pattern*
  (rule-name :pure-pattern
             (in-order [remove-expressions
                        evaluate-structure])))

(def ^{:doc "Inside a macro, syntax-quoted data is a deeply nested set of
          function calls.

          This resolves the specific structural calls to normal-looking forms
          and replaces any unquoted data with `identity` since unresolved
          function calls and other things are also mixed into the structure.

          The reason for this is to enable the pattern match compiler to extract
          correct pattern names from the expression before it is resolved within
          a macro. That lets us have nice matcher functions with the pattern
          variables bound directly since I can pull out the names they need to
          be bound to within the macro that defines it.

          If you call this directly outside of a macro, the input needs to be
          _double syntax quoted_ or you will just get `identity` back!"
       :arglists '([pattern])}
  pure-pattern
  pure-pattern*)
(reset! r/pure-pattern #'pure-pattern)


(def remove-symbol-namespaces
  (rule-name :remove-symbol-namespaces
             (directed
              (rule-list [(rule `(list ?->item)
                                `(list ~item))
                          (rule `(sequence ?->item)
                                `(sequence ~item))
                          (rule `(seq (concat ??->lists))
                                `(seq (concat ~@lists)))
                          (rule `(apply hash-set ?->item)
                                `(apply hash-set ~item))
                          (rule `(apply hash-map ?->item)
                                `(apply hash-map ~item))
                          (rule `(apply vector ?->item)
                                `(apply vector ~item))
                          (rule '(quote ?quoted)
                                (list 'quote
                                      (walk/postwalk (fn [x]
                                                       (if (symbol? x)
                                                         (symbol (name x))
                                                         x))
                                                     quoted)))]))))

(defmacro quo
  "Remove symbol namespaces.

  Useful for cleaning up namespaces in syntax-quoted input data. Otherwise, use
  [[sub]].

  Requires that the expression is syntax quoted. Does not perform any other
  transformation.

  Usage:

      (quo `(expt x ~(+ 1 1))"
  [expr]
  (remove-symbol-namespaces expr))

(defn expand-or [types results]
  (loop [[t & types] types
         [r & results] results]
    (if t
      (if (= '?? t)
        (or (seq (first r)) (recur types results))
        (if (ffirst r) (first r) (recur types results)))
      [])))

(defn expand-and [types results]
  (or
   (loop [[t & types] types
          [r & results] results
          value []]
     (if t
       (if (= '?? t)
         (when-let [v (seq (first r))]
           (recur types results v))
         (when (ffirst r)
           (recur types results (first r))))
       value))
   []))

(def do-unquote*
  (rule-name :do-unquote
             (rule-list [(rule '((?:literal clojure.core/unquote) ?x)
                               `(list ~x))
                         (rule '((?:literal clojure.core/unquote-splicing) ?x)
                               x)])))


(def unquote-all*
  (iterated-on-subexpressions do-unquote*))

(def to-syntax-quote*
  (rule-name :to-syntax-quote
             (rule-list [;; vector
                         (rule '[(?:* ?items)]
                               `(list (apply vector ~(seq (second (descend (seq items)))))))

                         ;; map
                         (rule '(?:chain (? _ map?) seq (?) (apply concat) ?items)
                               (let [items (second (descend items))]
                                 `(list (apply hash-map ~(seq items)))))

                         ;; set
                         (rule '(?:chain (? _ set?) seq ?items)
                               `(list (apply hash-set ~(seq (second (descend (seq items)))))))

                         ;; ignore unquotes
                         (rule '((?:literal clojure.core/unquote) ?x)
                               (list 'clojure.core/unquote x))
                         (rule '((?:literal clojure.core/unquote-splicing) ?x)
                               (list 'clojure.core/unquote-splicing x))

                         ;; list (must be placed after matchers since matchers can be lists)
                         (rule '((?:* ?->items))
                               `(list (seq (concat ~@items))))

                         ;; else
                         (rule '?x `(list '~x))])))

(def expand-pattern
  (rule-name :expand-pattern
             (directed
              (rule-list [do-unquote*

                          ;; var
                          (rule '(?:chain ?var matcher-type-for-dispatch ?)
                                `(list ~(var-name var)))

                          ;; segment
                          (rule '(?:chain ?var matcher-type-for-dispatch ??)
                                (var-name var))

                          ;; sequence
                          (rule '(?:as expr ((? op #{?:* ?:+}) ??pattern))
                                (let [names (distinct (mapcat pattern-args pattern))
                                      seqs (doall (map (fn [n] `(if (seqable? ~n) ~n (repeat ~n)))
                                                       names))
                                      expanded (descend pattern)]
                                  `(if (some seqable? ~(vec names))
                                     (mapcat (fn [~@names] ~@expanded)
                                             ~@seqs)
                                     (throw (ex-info (str "At least one sequence variable must be bounded.\n\n"
                                                          "If a variable `x` is not seqable it wrapped with "
                                                          "(repeat x), so the cause of this probem could be "
                                                          "that no expansion variables are sequential for the "
                                                          "repeat pattern.")
                                                     {:expression '~expr})))))

                          ;; group
                          (rule '((? op #{?:? ?:1}) ??->pattern)
                                `(seq (apply concat ~pattern)))

                          ;; and
                          (rule '(?:chain ?var matcher-type-for-dispatch &)
                                (let [types (doall (map (fn [v]
                                                          (list 'quote (matcher-type-for-dispatch v)))
                                                        (rest var)))
                                      results (doall (map (comp descend list) (rest var)))]
                                  `(expand-and (list ~@types) (list ~@results))))

                          ;; or
                          (rule '(?:chain ?var matcher-type-for-dispatch |)
                                (let [types (doall (map (fn [v]
                                                          (seq (list 'quote (matcher-type-for-dispatch v))))
                                                        (rest var)))
                                      results (doall (map (comp descend list) (rest var)))]
                                  `(expand-or (list ~@types) (list ~@results))))

                          ;; other
                          (rule '((?:literal ?:literal) ?value) `(list '~value))
                          (rule '((?:literal ?:restartable) ?->value) value)
                          (rule '((?:literal ?:chain) ?->value ??_) value)
                          (rule '((?:literal ?:as) ?name ?value)
                                (let [t (if (= '?? (matcher-type-for-dispatch value))
                                          '?? '?)
                                      name (if (= '? t)
                                             `(list ~name)
                                             name)]
                                  `(expand-or (list '~t '~t) (list (list ~name) ~(descend (list value))))))

                          ;; map
                          (rule '((?:literal ?:map) (?:* ?->k ?->v))
                                `(list (apply hash-map (seq (concat ~@(interleave k v))))))

                          ;; if
                          (rule '((?:literal ?:if) ?pred ?->then (?:? ?->else))
                                `(let [then# ~then]
                                   (if (apply ~pred then#) then# ~else)))

                          ;; when
                          (rule '((?:literal ?:when) ?pred ??->then)
                                `(let [then# ~then]
                                   (when (apply ~pred (first then#))
                                     (seq (apply concat then#)))))

                          to-syntax-quote*]))))

(def simplify-expr
  (rule-name :simplify-expr
             (rule-simplifier
              [(rule `(seq (concat)) nil)
               (rule `(seq (concat (?:* (list ?item))))
                     `(list ~@item))
               (rule `(seq (concat (?:* (list ?item)) ?x))
                     `(list* ~@item ~x))
               (rule `(apply ?f (list ??items)) `(~f ~@items))
               (rule '(quote (? x number?)) x)])))

(def simplify-more
  (rule-name :simplify-more
             (rule-simplifier
              [(rule `(list (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote (~@x*)))
               (rule `(vector (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote [~@x*]))
               (rule `(hash-set (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote #{~@x*}))
               (rule `(hash-map (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote {~@[] ~@x*}))])))

(def unwrap-list (rule-name :unwrap-list (rule-list [(rule `(list ?x) x)
                                                     (rule `(?:as expr ((? op #{if let seq}) ??rest))
                                                           `(first ~expr))
                                                     (rule `(? x symbol?) `(first ~x))])))

(def unwrap-quote (rule-name :unwrap-quote (rule `(~'quote ?x) x)))

(def qsub*
  (rule-name :qsub
             (in-order [expand-pattern
                        remove-symbol-namespaces
                        unwrap-list
                        simplify-expr
                        simplify-more])))
(reset! r/qsub* #'qsub*)

(def splice*
  (rule-name :splice
             (in-order [(directed to-syntax-quote*)
                        unquote-all*
                        unwrap-list
                        simplify-expr
                        simplify-more])))

(defmacro sub
  "Statically macroexpand substitution patterns expressed exactly like matcher
  patterns.

  This produces what I expect shoud be optimally fast substitutions, but differs
  from [[matches.substitute/substitute]] in that it requires that all substitution patterns
  must be bound, and will produce a compilation error if not."
  [form]
  (qsub* form))

(defn eval-spliced
  "Experimental. Uses [[spliced]] to transform regular lists, then uses eval to
  resolve spliced data. Doesn't resolve any data in the local scope."
  [x]
  (eval (splice* x)))

(defn spliced
  "A function that allows regular quoted lists to be spliced just like
  syntax-quoted ones, but only really works within macros because the spliced in
  data needs to be evaluated and it doesn't seem possible to do that at runtime
  except with [[eval]], which does not use the current evaluation scope. If that
  works for you, use [[eval-spliced]], but usually you will be better off with
  either the [[sub]] (recommended), or [[quo]] macros.

  This may eventually be useful together with SCI?"
  [form]
  (if (and (seqable? form) (= 'quote (first form)))
    (splice* (second form))
    form))
(reset! r/spliced #'spliced)
