(ns pattern.r3.rewrite
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
  (:require [pattern.match.core :refer [matcher-type-for-dispatch var-name matcher-mode
                                        named-matcher? simple-named-var?]]
            pattern.matchers ;; just to ensure the ns is loaded
            [pattern.r3.core :as r :refer [rule success name-rule pattern-args]]
            [clojure.walk :as walk]
            [pattern.r3.combinators :refer [descend
                                            descend-all
                                            rule-list in-order rule-simplifier
                                            simplifier
                                            on-subexpressions
                                            directed]]
            [pattern.util :as util]
            [clojure.string :as str]))

(def remove-expressions
  "Replace all unquoted expressions with 'identity but leave the structure of the
  expression unmodified."
  (name-rule :remove-expressions
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
                          (rule `(apply (| hash-map array-map) ?->v)
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
  (name-rule :evaluate-structure
             (directed
              (rule-list [(rule `(seq ?->s) s)
                          (rule `(sequence ?->s) s)
                          (rule `(list ?->item) (list item))
                          (rule `(concat ??->lists) (apply concat lists))
                          (rule `(apply hash-set ?->v) (set v))
                          (rule `(apply vector ?->v) (vec v))
                          (rule '(quote ?quoted) (success quoted))]))))

(def pure-pattern
  ^{:doc "Inside a macro, syntax-quoted data is a deeply nested set of
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
  (name-rule :pure-pattern
             (in-order [remove-expressions
                        evaluate-structure])))

(reset! r/pure-pattern #'pure-pattern)

(defn array-or-hash-map [& items]
  (let [hm (apply hash-map items)]
    (if (< (count items) 16)
      (apply array-map items)
      ;; TODO: are these assumptions sound? That if the items are not in the
      ;; hash-map's order already then they never were in a hash map and so they
      ;; are in their original order and can be safely put into an array map?
      ;;
      ;; The idea is that if items come out in an array map, their order may be
      ;; considered significant. I want to use this in a simple {...} matcher that
      ;; will include metadata indicating whether the arg order is stable.
      ;;
      ;; Maybe a better solution to this is to revisit the pure-pattern idea instead,
      ;; which is what this needs to cater to.
      (if (= (keys hm) (take-nth 2 items))
        hm
        (apply array-map items)))))

(def remove-symbol-namespaces
  (name-rule :remove-symbol-namespaces
             (directed
              (rule-list [(rule `(list ?->item)
                                `(list ~item))
                          (rule `(sequence ?->item)
                                `(sequence ~item))
                          (rule `(seq (concat ??->lists))
                                `(seq (concat ~@lists)))
                          (rule `(apply hash-set ?->item)
                                `(apply hash-set ~item))
                          (rule `(apply (| hash-map array-map) ?->item)
                                (if (::ordered (meta item))
                                  `(apply array-map ~(with-meta item {::ordered true}))
                                  `(apply array-or-hash-map ~item)))
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

      (quo `(expt x ~(+ 1 1)))"
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
  (name-rule :do-unquote
             (rule-list [(rule '((?:literal clojure.core/unquote) ?x)
                               `(list ~x))
                         (rule '((?:literal clojure.core/unquote-splicing) ?x)
                               x)])))


(def unquote-all*
  (simplifier do-unquote*))

(def to-syntax-quote*
  (name-rule :to-syntax-quote
             (rule-list [;; vector
                         (rule '[(?:* ?items)]
                               `(list (apply vector ~(seq (second (descend (seq items)))))))

                         ;; map
                         (rule '(?:chain (? _ map?) seq (?) (apply concat) ?items)
                               (let [items (second (descend items))]
                                 `(list (apply array-map
                                               ~(with-meta items {::ordered true})))))

                         ;; set
                         (rule '(?:chain (? _ set?) seq ?items)
                               `(list (apply hash-set ~(seq (second (descend (seq items)))))))

                         ;; ignore unquotes
                         (rule '((?:literal clojure.core/unquote) ?x)
                               (list 'clojure.core/unquote x))
                         (rule '((?:literal clojure.core/unquote-splicing) ?x)
                               (list 'clojure.core/unquote-splicing x))

                         (rule '((?:literal ?:list) (?:* ?->items))
                               `(list (seq (concat ~@items))))

                         ;; list (must be placed after matchers since matchers can be lists)
                         (rule '((?:* ?->items))
                               `(list (seq (concat ~@items))))

                         ;; else
                         (rule '?x `(list '~x))])))

(def ^:dynamic *on-marked-insertion* identity)

(def expand-pattern
  (name-rule :expand-pattern
    (directed
      (rule-list [do-unquote*

                  ;; var
                  (rule '(?:chain ?var matcher-type-for-dispatch ?)
                    (let [n (var-name var)]
                      (if (= '_ n)
                        ()
                        (if (str/includes? (or (matcher-mode var) "") "<-")
                          `(list (~*on-marked-insertion* ~(var-name var)))
                          `(list ~(var-name var))))))

                  ;; segment
                  (rule '(?:chain ?var matcher-type-for-dispatch ??)
                    (let [n (var-name var)]
                      (if (= '_ n)
                        ()
                        (if (str/includes? (or (matcher-mode var) "") "<-")
                          `(map ~*on-marked-insertion* ~(var-name var))
                          (var-name var)))))

                  (rule '((?:literal ?:<-) ?->x)
                    `(map ~*on-marked-insertion* ~x))

                  ;; sequence
                  (rule '(?:as expr (| ((? op #{?:* ?:+}) ??pattern)
                                      ((? op #{?:n}) ?_ ??pattern)))
                    (let [names (pattern-args pattern)
                          seqs (doall (map (fn [n]
                                             `(if (seqable? ~n)
                                                ~n
                                                (repeat ~n)))
                                        names))
                          expanded (descend pattern)]
                      `(if (some seqable? ~(vec names))
                         (mapcat (fn [~@names] ~@expanded)
                           ~@seqs)
                         (throw (ex-info (str "At least one sequence variable must be bounded.\n\n"
                                           "If a variable `x` is not seqable it wrapped with "
                                           "(repeat x), so the cause of this problem could be "
                                           "that no expansion variables are sequential for the "
                                           "repeat pattern.")
                                  {:expression '~expr})))))

                  ;; optional
                  (rule '((?:literal ?:?) ??pattern)
                    (let [pa (map (fn [arg] `(some? ~arg))
                               (pattern-args pattern))
                          expanded (descend-all pattern)]
                      `(if (and ~@pa)
                         (let [p# (seq (apply concat ~expanded))]
                           (when (seq (filter some? p#))
                             p#)))))

                  (rule '((?:literal ?:1) ??->pattern)
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
                      (if (or (= false (last var)) (nil? (last var)))
                        (throw (ex-info "The expression (| ... false) will not return a false literal. You won't get the expected result here, you will get a 0-length replacement."
                                 {:expression var}))
                        `(expand-or (list ~@types) (list ~@results)))))

                  ;; other
                  (rule '((?:literal ?:literal) ?value) `(list '~value))
                  (rule '((?:literal ?:=) ?value) `(list '~value))
                  (rule '((?:literal ?:restartable) ?->value) value)
                  (rule '((?:literal ?:chain) ?->value ??_) value)
                  (rule '((?:as op (| (?:literal ?:as) (?:literal ?:as*))) ?name ?value)
                    (let [t (if (or (= '?:as* op)
                                  ;; this behavior is a bit ambiguous but it's how ?:as was originally defined
                                  ;; before ?:as* was invented.
                                  (= '?? (matcher-type-for-dispatch value)))
                              '?? '?)
                          name (if (= '? t)
                                 `(list ~name)
                                 name)]
                      `(expand-or (list '~t '~t) (list (list ~name) ~(descend (list value))))))

                  ;; map
                  (rule '((?:literal ?:map) (?:* ?->k ?->v))
                    `(list (apply array-map
                             ~(with-meta `(seq (concat ~@(interleave k v)))
                                {::ordered true}))))

                  ;; exploded map
                  (rule '((?:literal ??:map) (?:* ?->k ?->v))
                    `(seq (concat ~@(interleave k v))))

                  (rule '((| (?:literal ?:*map) (?:literal ?:map*) (?:literal ?:+map) (?:literal ?:map+)) ?ks ?vs)
                    (let [ks (var-name ks)
                          vs (var-name vs)]
                      (if (or (= '_ ks) (= '_ vs))
                        `(list (apply array-map (list)))
                        `(list (apply array-map
                                 ~(with-meta `(interleave ~ks ~vs)
                                    {::ordered true}))))))

                  (rule '((?:literal ?:set) ?items)
                    (let [items (var-name items)]
                      (if (= '_ items)
                        ;; TODO: should this be an empty set?
                        `(list (set (list)))
                        `(list (set ~items)))))

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
  (name-rule :simplify-expr
             (rule-simplifier
              [(rule `(seq (concat)) nil)
               (rule `(seq (concat (?:* (list ?item))))
                     `(list ~@item))
               (rule `(seq (concat (?:* (list ?item)) ?x))
                     `(list* ~@item ~x))
               (rule `(apply ?f (list ??items)) `(~f ~@items))
               (rule '(quote (? x number?)) x)])))

(def simplify-more
  (name-rule :simplify-more
             (rule-simplifier
              [(rule `(list (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote (~@x*)))
               (rule `(vector (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote [~@x*]))
               (rule `(hash-set (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote #{~@x*}))
               (rule `(hash-map (?:* (?:or (~'quote ?x*) (? x* number?))))
                     `(~'quote {~@[] ~@x*}))])))

(def unwrap-list
  (name-rule :unwrap-list
             (rule-list [(rule `(list ?x) x)
                         (rule `(?:as expr ((? op #{if let seq}) ??rest))
                               `(first ~expr))
                         (rule `(? x symbol?) `(first ~x))])))

(def unwrap-quote (name-rule :unwrap-quote (rule `(~'quote ?x) x)))

(def scheme-style
  (on-subexpressions
   (rule-list
    (rule '[??before ?form (?:chain (? _ symbol?) name "...") ??after]
          `[~@before (~'?:* ~form) ~@after])
    (rule '(??before ?form (?:chain (? _ symbol?) name "...") ??after)
          `(~@before (~'?:* ~form) ~@after)))))
(reset! r/scheme-style #'scheme-style)

(def qsub*
  (name-rule :qsub
             (in-order [scheme-style
                        expand-pattern
                        remove-symbol-namespaces
                        unwrap-list
                        simplify-expr
                        simplify-more])))
(reset! r/qsub* #'qsub*)

(def qsub+
  "Same as qsub* but keeps symbol namespaces"
  (name-rule :qsub+
             (in-order [scheme-style
                        expand-pattern
                        unwrap-list
                        simplify-expr
                        simplify-more])))

(def splice*
  (name-rule :splice
             (in-order [(directed to-syntax-quote*)
                        unquote-all*
                        unwrap-list
                        simplify-expr
                        simplify-more])))

(defmacro sub-
  "Just like [[sub]] but strips all namespaces from symbols."
  ([form]
   (qsub* form))
  ([f form]
   (binding [*on-marked-insertion* f]
     (qsub* form))))

(defmacro sub
  "Statically macroexpand substitution patterns expressed exactly like matcher
  patterns.

  This produces what I expect shoud be optimally fast substitutions, but differs
  from [[pattern.substitute/substitute]] in that it requires that all substitution patterns
  must be bound, and will produce a compilation error if not.

  The arity 2 version allows substitutions to be transformed by the supplied
  function before being inserted if they are marked with <- or wrapped with (?:<- ...)"
  ([form]
   (qsub+ form))
  ([f form]
   (binding [*on-marked-insertion* f]
     (qsub+ form))))

(defmacro sub+
  "Same as [[sub]]. Here for backward compatibility"
  [& etc]
  `(sub ~@etc))

(defmacro rmeta
  "Expands to (meta (:rule/datom %env))"
  []
  `(meta (:rule/datum ~'%env)))

(defmacro subm
  "Perform substitution and attach the provided metadata.

  If called arity-1, copy the rule's original matching form's metadata onto the
  resulting form, using rmeta to capture the metadata."
  ([form]
   `(subm ~form (rmeta)))
  ([form metadata]
   `(with-meta (sub ~form) ~metadata)))

(defmacro subm+
  "Like [[subm]] but checks that form is an IObj before attaching metadata.

   Useful for generated expressions."
  ([form]
   `(subm+ ~form (rmeta)))
  ([form metadata]
   `(let [form# (sub ~form)]
      (if (instance? clojure.lang.IObj form#)
        (with-meta form# ~metadata)
        form#))))

;; TODO: If the regular sub and subm methods all retained namespace, would that
;; break anything? I think the behaviour may be leftover from the earliest
;; versions of this functionality which tried to build off of stock
;; backtick-quoted data, which was loaded with namespaces everywhere.

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

(def remove-matcher-ns
  "This makes (some.ns/? some.ns/x) look like (? x), etc when displaying rules."
  (on-subexpressions
   (rule-list [(rule '(? v ~simple-named-var?)
                     (symbol (name v)))
               (rule '(& (? _ ~named-matcher?)
                         (?op ?n ??more))
                     (sub (~(symbol (name op)) ~(symbol (name n)) ??more)))])))

(def cleanup-rule-pattern
  "Makes syntax-quoted rule patterns presentable"
  (in-order [evaluate-structure
             remove-matcher-ns]))

(def rule-src
  "Makes syntax-quoted rules presentable"
  (rule '(rule ?pattern ??body)
        (sub (rule ~(cleanup-rule-pattern pattern) ~@(map evaluate-structure body)))))
(reset! r/rule-src #'rule-src)

(def add-env-args*
  "The rewrite used by a macro that recursively adds metadata to rules before
  the rule macro runs. It uses the metadata to let-bind values from %env within
  rule-handlers."
  (directed
    (rule-list
      (rule '((?:as op (| rule-list in-order on-subexpressions)) (| [??rules] ??rules))
        (let [rules (for [r rules]
                      (first (descend r %env)))]
          (sub (?op ??->rules))))
      (rule '(rule ?pattern ??more)
        ;; metadata-only change needs `success` to stick!
        (success
          (sub (rule ~(vary-meta pattern assoc :env-args (:env-args %env))
                 ??more))))
      (rule '(?combinator-name ?->rule)))))

(defmacro with-env-args
  "Attach :env-args metadata to rules to enable convenient binding of env data
  in the rule handlers."
  [bindings rules]
  (first (add-env-args* rules {:env-args bindings})))
