(ns pattern.r3.combinators
  (:refer-clojure :exclude [trampoline])
  (:require [pattern.match.core :refer [run-matcher]]
            [pattern.r3.rule :refer [*debug-rules* run-rule make-rule post-process]]
            [pattern.substitute :refer [substitute]]
            [pattern.types :refer [rule-combinator? child-rules recombine ->Success]]
            [pattern.util :refer [meta? equiv?]]
            [clojure.string :as str]
            [genera :refer [trampoline bouncing]]
            [clojure.walk :as walk]
            [clojure.zip :as z :refer [zipper]])
  (:import clojure.lang.IObj))

;; TODO: I'm checking in many places whether the datum or env changed. Would things work
;; if I consolidated that into a check for `identical?`?

(defn rule-zipper
  "Construct a zipper object for rule combinators to enable customization of rules, attaching
  custom metadata, etc."
  [rc]
  (zipper rule-combinator? child-rules recombine rc))

(defn rule-list
  "Try each of the rules in order top-down.

  If any rule succeeds, return that result. If a rule matches but does not
  succeed, continues down the list.

  Each rule can itself be any rule-combinator."
  [& rules]
  (let [rules (flatten rules)]
    (with-meta
      (fn do-rule-list
        ([data] (first (run-rule do-rule-list data nil)))
        ([data env] (run-rule do-rule-list data env))
        ([data env succeed fail]
         (do-rule-list data env nil succeed fail))
        ([data env events succeed fail]
         (letfn [(per-rule [[r :as rules]]
                   (when (and *debug-rules* r) (prn 'try (:pattern (:rule (meta r)))))
                   (if (seq rules)
                     (r data env events succeed
                        #(bouncing (per-rule (rest rules))))
                     (fail)))]
           (trampoline per-rule rules))))
      {:rule {:rule-type ::rule-list
              :rules (mapv meta rules)}
       `child-rules (fn [_] rules)
       `recombine (fn [_ rules]
                    (rule-list rules))})))

(defn rule-list!
  "Like rule-list, but throws an exception if no rule matches.

  Each rule can itself be any rule-combinator."
  [& rules]
  (rule-list (concat rules [(make-rule '?_ (fn [env dict]
                                             (throw (ex-info "No matching clause" env))))])))

(defn default
  "Returns a rule that always returns the given value"
  [value]
  (make-rule '?_ (fn [env dict] (->Success value))
    {:src (list 'success value)}))

(defn in-order
  "Runs each of the rules in the list in a chain. If any rule succeeds, the
  subsequent rules are run with the new value. If a rule fails, the current
  value does not change and the next rule is run.

  Each rule can itself be any rule-combinator.

  opts:

    :equiv? default: [[equiv?]]"
  [opts & rules]
  (let [[opts rules] (if (map? opts)
                       [opts rules]
                       [{} (cons opts rules)])
        equiv? (:equiv? opts equiv?)
        equiv-ne? (equiv? :no-env)
        rules (flatten rules)
        rc (count rules)]
    (letfn [(per-rule [datum prev-env events [r :as rules] n]
              (when *debug-rules* (println (str "#" (inc n) "/" rc " try" (:pattern (:rule (meta r))))))
              (if (seq rules)
                (r datum
                   prev-env events
                   (fn [result env _]
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " succeded")))
                     (let [[datum env] (if (equiv-ne? datum prev-env result env)
                                         ;; BUG? returning the modified env even if returning the old value
                                         [datum env] [result env])]
                       (bouncing (per-rule datum env events
                                   (next rules) (inc n)))))
                   (fn []
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " failed")))
                     (bouncing (per-rule datum prev-env events (next rules) (int n)))))
                (do
                  (when *debug-rules* (println (str "#" (inc n) "/" rc " ran out of rules")))
                  [datum prev-env])))]
      (with-meta
        (fn do-in-order
          ([data] (first (run-rule do-in-order data nil)))
          ([data env] (run-rule do-in-order data env))
          ([data env succeed fail]
           (do-in-order data env nil succeed fail))
          ([orig-datum orig-env events succeed fail]
           (let [[result env] (trampoline per-rule orig-datum orig-env events rules 0)]
             (if (equiv? orig-datum orig-env result env)
               (fail)
               (succeed result env fail)))))
        {:rule {:rule-type ::in-order
                :opts opts
                :rules (mapv meta rules)}
         `child-rules (fn [_] rules)
         `recombine (fn [_ rules]
                      (in-order opts rules))}))))

(defn guard [f rule]
  (with-meta
    (fn do-predicate
      ([data] (first (run-rule do-predicate data nil)))
      ([data env] (run-rule do-predicate data env))
      ([data env succeed fail]
       (do-predicate data env nil succeed fail))
      ([datum env events succeed fail]
       (if (f datum env)
         (rule datum env events succeed fail)
         (fail))))
    {:rule {:rule-type ::guard
            :predicate f
            :rule rule}
     `child-rules (fn [_] [rule])
     `recombine (fn [_ rules]
                  (if (next rules)
                    (guard f (rule-list rules))
                    (guard f (first rules))))}))

(defn n-times
  "Iteratively apply the rule n times.

  The rule can be any rule-combinator."
  [n rule]
  (vary-meta
   (in-order (repeat n rule))
   assoc-in [:rule :rule-type] ::n-times))

(def ^:dynamic *descend*
  (fn ([e] e) ([e env] [e env])))

(defn descend
  "If passing in an env, pass it as the first arg since within a rule handler,
  the expression part is likely to be a large hairy expression, and the env
  aspect will be easily lost at the end of it. "
  ([expression]
   ;; should not bounce through descend, so don't need to check for a function passing through.
   (first (*descend* expression nil)))
  ([expression env]
   (*descend* expression env)))

(defn in
  "Descend with an env without retaining the resulting env."
  [x env]
  (first (descend x env)))

(defn descend-all
  "Descend each element in e*, threading the env and returning the result.

  Like descend, if called without env it just returns the resulting expression
  and doesn't return the env, but if called with an env, it returns
  [result env].

  An alternative strategy would be to merge the resulting envs, but that could
  require a custom merge strategy, so isn't provided as a built-in helper."
  ([e*]
   (first (descend-all e* {})))
  ([e* env]
   (let [descend *descend*]
     (reduce (fn [[e* env] e]
               (let [[e env] (descend e env)]
                 [(conj e* e) env]))
       [[] env]
       e*))))

(def ^:dynamic *descent-depth* nil)
(def ^:dynamic *do-mutual-descent* nil)

(defn- directed:extend-rule-metadata [rule-meta {:keys [fn-map descend mutual on-rule-meta]
                                                 :or {on-rule-meta (fn [from to] to)}}]
  ;; These letfns could be refactored but the subtle differences are annoying
  ;; and they're not used a lot...
  (letfn [(detect-mode [rule-meta mode-type mode-string data]
            ;; capture a list of var names with the given mode-type
            (update rule-meta mode-type
                    merge
                    (reduce-kv (fn [m n modes]
                                 (if (and modes (str/includes? modes (name mode-string)))
                                   (assoc m n (data n))
                                   m))
                               {} (:var-modes rule-meta))))
          (detect-meta [rule-meta mode-type meta-key f selection]
            (if selection
              (update rule-meta mode-type merge
                      (reduce-kv (fn [m n attr]
                                   (if-let [sel (some selection (f attr))]
                                     (assoc m n (if (map? selection)
                                                  sel
                                                  meta-key))
                                     m))
                                 {} (meta-key rule-meta)))
              rule-meta))
          (detect-name [rule-meta mode-type selection]
            (if selection
              (update rule-meta mode-type merge
                      (reduce (fn [m name]
                                (if-let [sel (selection name)]
                                  (assoc m name (if (map? selection) sel :name))
                                  m))
                              {} (:var-names rule-meta)))
              rule-meta))]
    (on-rule-meta
     rule-meta
     (let [r (-> rule-meta
                 ;; marked with -> for descent.
                 (detect-mode :descending? "->" identity)
                 ;; marked with $ for mutual recursion.
                 (detect-name :descending? (:name descend))
                 (detect-meta :descending? :var-abbrs identity (:abbr descend))
                 (detect-meta :descending? :var-abbrs identity (:abbr (:descend rule-meta)))
                 (detect-meta :descending? :var-prefixes #(map symbol %) (:prefix descend))
                 (detect-mode :mutual? "$" meta)
                 (detect-name :mutual? (:name mutual))
                 (detect-meta :mutual? :var-abbrs identity (:abbr mutual))
                 (detect-meta :mutual? :var-abbrs identity (:abbr (:mutual rule-meta)))
                 (detect-meta :mutual? :var-prefixes #(map symbol %) (:prefix mutual))
                 (assoc :transform? {}))
           r (reduce (fn [rule-meta [mode-string f]]
                       (detect-mode rule-meta :transform? (name mode-string) (constantly f)))
                     r fn-map)
           ;; descend in var-name order
           r (assoc r :active (map (set (concat (keys (:descending? r))
                                                (keys (:transform? r))))
                                   (:var-names rule-meta)))]
       (cond-> r
         ;; If the datum will change after the initial match (via ?->x style
         ;; rules), and it's possible that (success) arity 0 will be called, the
         ;; datum needs to have the new values substituted into it.
         ;; The primary use case for this used to be pattern-only rules, but it is
         ;; also possible for rules to return (success).
         (and (:may-call-success0? r)
              (seq (:active r)))
         (assoc :substitute (substitute (:pattern rule-meta))))))))

(defn- directed:extended [rule opts]
  (loop [rz (rule-zipper rule)]
    (cond (z/end? rz) (z/root rz)
          (z/branch? rz) (recur (z/next rz))
          (nil? (z/node rz)) (recur (z/next rz))
          :else (recur (z/next (z/edit rz vary-meta update :rule
                                       #(directed:extend-rule-metadata % opts)))))))

(defn- directed:descend-marked [apply-rules rule-meta dict env depth]
  (let [{:keys [active descending? mutual? transform? substitute]} rule-meta
        apply-rules (partial apply-rules (inc depth))
        mutual-fn *do-mutual-descent*]
    (binding [*descend* apply-rules] ;; TODO: bind descend in do-mutual-descent, too
      (reduce (fn [[dict env substitute] k]
                (if-let [match (dict k)]
                  (try
                    (let [enter (cond (and mutual-fn (mutual? k))
                                      (partial mutual-fn (mutual? k) (inc depth))
                                      (descending? k) apply-rules
                                      :else vector)
                          enter (if-let [f (transform? k)]
                                  (comp (fn [[v e]] [(f v) e]) enter)
                                  enter)]
                      (if (#{'?? '?:*} (:type match))
                        ;; TODO: metadata could capture sequence nesting level, which
                        ;; would make this more powerful. Now it only supports 1
                        ;; level of nesting, so some patterns are not correctly
                        ;; represented.
                        (let [[v env] (reduce (fn [[v env] d]
                                                (let [[r env] (enter d env)]
                                                  [(conj v r) env]))
                                        [[] env] (:value match))]
                          [(assoc-in dict [k :value] v) env substitute])
                        (let [[v env] (enter (:value match) env)]
                          [(assoc-in dict [k :value] v) env substitute])))
                    (catch Exception e
                      (println "Unwinding through: " k)
                      (clojure.pprint/pprint match)
                      (throw e)))
                  [dict env substitute]))
              [dict env substitute] active))))

(defn directed
  "Recurs depth-first, but only into marked subexpressions.

  Marking a subexpression looks like ?->x or ??->x
  (ie. marked with -> matcher mode), so a matcher like ?y would not get recurred
  into.

  Does not iteratively descend into any expressions returned by matchers. To do
  any iterative descent, call `descend` within the handler on the subexpressions
  you wish to descend into.

  You can also use opts to mark vars to descend by :name, :prefix or
  :abbr. Look at your rule metadata to see how the var names get that info
  extracted. For example to descend all rules that have an abbr of `e`, use

      {:descend {:abbr #{'e}}}

  Which would cause all descend the same as the following rule even if that rule
  had no -> markings:

      (rule '[?->e ?->e0 ?->e123 ?no (?-> e*) ?->e:ok ?e-no ?e0:no])

  You can provide an optional :fn-map via the opts argument, which is a map from
  additional mode symbols to functions that are applied to a captured match
  before it is passed to the rule handler. Only one function per symbol is
  allowed.

  If a function is provided as the opts argument, it is treated as if you had
  passed in {:fn-map {'>- f}}, and if subexpressions are marked with >-, the
  expression, or the result of traversing into the expression if it is also
  marked with -> , will be passed to the function f. If no function is provided,
  [[identity]] is used.  In this case, the matcher would look like one of ?>-,
  ??>-, ?>-> (note this is a shortened form), ?>-->, ??->>-, etc. The order of
  >- and -> does not matter.  If any other symbols other than >- are provided in
  the :fn-map key of opts, the above description applies with the symbol you
  used.

  You can provide a function on the :on-rule-meta opts key to make any
  arbitrary changes to rule metadata. The default is:

      (fn on-rule-meta [rule-meta-before rule-meta-after]
        rule-meta-after)

  The rule argument is typically a rule-list of simple rules, but in theory
  any type of rule combinator should work, however determining the resulting
  behavior may be tricky in some cases..."
  ([rule]
   (directed nil rule))
  ([opts raw-rule]
   (let [opts (if (fn? opts)
                {:fn-map {">-" opts}}
                opts)
         equiv? (:equiv? opts equiv?)
         rule (directed:extended raw-rule opts)]
     (with-meta
       (fn do-on-marked
         ([data] (first (run-rule do-on-marked data nil)))
         ([data env] (run-rule do-on-marked data env))
         ([data env succeed fail]
          (do-on-marked data env nil succeed fail))
         ([orig-datum orig-env events y n]
          (letfn [(apply-rules [depth datum env]
                    (when *debug-rules*
                      (prn (symbol (apply str (repeat depth " "))) '=== datum))
                    (rule datum env
                      (assoc events
                        :on-match
                        (fn directed:on-match [r match-dict]
                          (let [[match-dict env substitute]
                                (directed:descend-marked apply-rules (:rule (meta r))
                                  match-dict env depth)
                                ;; Per the note in directed:extend-rule-metadata :
                                ;; If the datum will change after the initial match, and it's possible
                                ;; that (success) arity 0 will be called, the datum needs to have the
                                ;; new values substituted into it:
                                datum (if substitute
                                        (first (post-process r
                                                (substitute
                                                  (fn [k none] (:value (match-dict k) none))
                                                  nil)
                                                datum env env))
                                        datum)]
                            [datum match-dict env])))
                      (fn [d env _] [d env])
                      (fn [] [datum env])))]
            (binding [*descend* (partial apply-rules (inc (or *descent-depth* 0)))]
              (let [res (apply-rules (or *descent-depth* 0) orig-datum orig-env)
                    [result env] res]
                (if (equiv? orig-datum orig-env result env)
                  (n)
                  (y result env n)))))))
       (-> (meta rule)
           (assoc-in [:rule :rule-type] ::directed)
           (merge {`child-rules (fn [_] [rule])
                   `recombine (fn [_ rules]
                                (if (next rules)
                                  (directed opts (rule-list rules))
                                  (directed opts (first rules))))}))))))

(defn on-mutual
  "The idea is that you can create a group of named rule sets where matchers are
  tagged with metadata and a matcher mode that tells this system to switch which
  rule set is applied for subexpressions of the given type. Effectively this
  lets you switch between expression types (or dialects?)  when applying rules
  to an expression.

  This is currently done in a somewhat simplistic way with bound variables
  because I'm not exactly sure how it should be structured but eventually it
  should be done without the need for extra global state like this.  "
  ([initial-form name-rule-pairs]
   (on-mutual equiv? initial-form name-rule-pairs))
  ([equiv? initial-form name-rule-pairs]
   (let [forms (if (map? name-rule-pairs)
                 name-rule-pairs
                 (apply hash-map name-rule-pairs))]
     (letfn [(switch-branch [{:keys [form-name]} depth datum env]
               (let [rule (or (forms form-name)
                            (when (vector? form-name) (forms (second form-name))))]
                 ;; TODO: probably want to just keep on the same branch if there
                 ;; is no option? Or maybe don't descend?
                 (if rule
                   (binding [*descent-depth* depth]
                     (run-rule rule datum env))
                   [datum env])))]
       (with-meta
         (fn do-mutual
           ([data] (first (run-rule do-mutual data nil)))
           ([data env] (run-rule do-mutual data env))
           ([data env succeed fail]
            (do-mutual data env nil succeed fail))
           ([orig-datum orig-env events y n]
            (binding [*do-mutual-descent* switch-branch]
              ;; TODO: how does events fit here?
              (let [[result env] (switch-branch {:form-name initial-form} 0 orig-datum orig-env)]
                (if (equiv? orig-datum orig-env result env)
                  (n)
                  (y result env n))))))
         ;; TODO: how does recombine work for this combinator? Or does it at all??
         {:rule {:rule-type ::on-mutual
                 :initial-form initial-form
                 :name-rule-pairs (reduce-kv (fn [m k v]
                                               (assoc m k (meta v)))
                                    {} name-rule-pairs)}})))))

;; TODO: add equiv to meta, and use it in rebuild

(defn- empty!
  "Map entries don't implement empty. I need vectors without their metadata."
  [x]
  (cond (map-entry? x) []
        (vector? x) []
        :else (empty x)))

(defn- try-subexpressions [equiv-ne? the-rule datum orig-env events]
  (if (and (seqable? datum) (not (string? datum)))
    (let [[result env] (reduce (fn [[result prev-env] d]
                                 (let [[r env] (run-rule the-rule d events prev-env)]
                                   [(conj result r) env]))
                         [(empty! datum) orig-env] datum)
          result (if (list? result) (reverse result) result)]
      (if (equiv-ne? datum orig-env result env)
        ;; BUG? returning modified env even on no change
        [datum env #_orig-env]
        [(if (meta result)
           result
           (if (instance? IObj result)
             (with-meta result (meta datum))
             result))
         env]))
    [datum orig-env]))

(defn on-subexpressions
  "Run the given rule combinator on all subexpressions depth-first."
  ([the-rule]
   (on-subexpressions equiv? the-rule))
  ([equiv? the-rule]
   (let [equiv-ne? (equiv? :no-env)]
     (with-meta
       (fn do-on-subexpr
         ([data] (first (run-rule do-on-subexpr data nil)))
         ([data env] (run-rule do-on-subexpr data env))
         ([data env succeed fail]
          (do-on-subexpr data env nil succeed fail))
         ([datum orig-env events y n]
          ;; TODO: how does events fit?
          (letfn [(on-subex-expr [datum subex-env events on-result fail]
                    (let [[done sx-env] (try-subexpressions equiv-ne? on-subex-expr datum subex-env events)
                          ;; BUG? no equiv? check against the orig datum/subex-env here?
                          [answer env] (run-rule the-rule done events sx-env)]
                      ;; Which env would even be compared in equiv? is undefined in original code...
                      (if (equiv-ne? done sx-env answer env)
                        ;; BUG? using the modified env even with no changes???
                        (on-result done env #_sx-env fail)
                        (on-result answer env fail))))]
            (let [[done env] (run-rule on-subex-expr datum events orig-env)]
              (if (equiv? datum orig-env done env)
                (n)
                (y done env n))))))
       {:rule (assoc (meta the-rule)
                :equiv? equiv?
                :rule-type ::on-subexpressions)
        `child-rules (fn [_] [the-rule])
        `recombine (fn [_ rules]
                     (if (next rules)
                       (on-subexpressions equiv? (rule-list rules))
                       (on-subexpressions equiv? (first rules))))}))))

(defn iterated
  "Run the given rule combinator repeatedly until running the rule makes no
  further changes."
  ([the-rule]
   (iterated equiv? the-rule))
  ([equiv? the-rule]
   (let [equiv-ne? (equiv? :no-env)]
     (with-meta
       (fn do-iter
         ([data] (first (run-rule do-iter data nil)))
         ([data env] (run-rule do-iter data env))
         ([data env succeed fail]
          (do-iter data env nil succeed fail))
         ([datum orig-env events y n]
          (letfn [(iterating [datum prev-env events on-result f]
                    (let [[answer env] (run-rule the-rule datum events prev-env)]
                      (if (equiv-ne? datum prev-env answer env)
                        ;; BUG? returning modified env?
                        (on-result datum env #_prev-env f)
                        (recur answer env events on-result f))))]
            (let [[done env] (run-rule iterating datum events orig-env)]
              (if (equiv? datum orig-env done env)
                (n)
                (y done env n))))))
       {:rule (assoc (meta the-rule)
                :equiv? equiv?
                :rule-type ::iterated)
        `child-rules (fn [_] [the-rule])
        `recombine (fn [_ rules]
                     (if (next rules)
                       (iterated equiv? (rule-list rules))
                       (iterated equiv? (first rules))))}))))


(defn simplifier
  "Run the given rule combinator repeatedly depth-first on all subexpressions
  until running the rule makes no further changes at each level."
  ([the-rule]
   (simplifier equiv? the-rule))
  ([equiv? the-rule]
   (let [equiv-ne? (equiv? :no-env)]
     (with-meta
       (fn enter-simplifier
         ([data] (first (run-rule enter-simplifier data nil)))
         ([data env] (run-rule enter-simplifier data env))
         ([data env succeed fail]
          (enter-simplifier data env nil succeed fail))
         ([datum orig-env events y n]
          (let [on-simplifier-expr
                (fn on-simplifier-expr [datum simp-env events on-result f]
                  (let [[done sub-env] (try-subexpressions equiv-ne? on-simplifier-expr datum simp-env events)
                        ;; odd there is no equiv check here...
                        [answer env] (run-rule the-rule done events sub-env)]
                    (if (equiv-ne? done sub-env answer env)
                      ;; BUG? returning modified env?
                      (on-result done env #_sub-env f)
                      (on-simplifier-expr answer env events on-result f))))]
            (let [[done env] (run-rule on-simplifier-expr datum events orig-env)]
              (if (equiv? datum orig-env done env)
                (n)
                (y done env n))))))
       {:rule (assoc (meta the-rule)
                :equiv? equiv?
                :rule-type ::simplifier)
        `child-rules (fn [_] [the-rule])
        `recombine (fn [_ rules]
                     (if (next rules)
                       (simplifier equiv? (rule-list rules))
                       (simplifier equiv? (first rules))))}))))

(defn prewalk-simplifier
  "Run the given rule combinator repeatedly, then continue on a prewalk descent
  of all subexpressions until running the rule makes no further changes at each
  level.

  This is the same strategy that Clojure's macroexpansion uses.

  You can provide a [[walk]] argument to use a custom variant of clojure.walk/walk."
  ([the-rule]
   (prewalk-simplifier walk/walk the-rule))
  ([walk the-rule]
   (prewalk-simplifier equiv? walk the-rule))
  ([equiv? walk the-rule]
   (let [equiv-ne? (equiv? :no-env)]
     (with-meta
       (fn enter-prewalk-simplifier
         ([data] (first (run-rule enter-prewalk-simplifier data nil)))
         ([data env] (run-rule enter-prewalk-simplifier data env))
         ([data env succeed fail]
          (enter-prewalk-simplifier data env nil succeed fail))
         ([datum orig-env events y n]
          (let [env (volatile! orig-env)]
            (letfn [(walker [datum0]
                      (loop [datum0 datum0
                             env0 @env
                             [datum1 env1] (run-rule the-rule datum0 events env0)]
                        (if (equiv-ne? datum0 env0 datum1 env1)
                          ;; descend. When done then:  (on-result datum1 env1)))
                          (do (vreset! env env1)
                              (walk walker identity datum1))
                          (recur datum1 env1 (run-rule the-rule datum1 env1)))))]
              (let [answer (walker datum)]
                (if (equiv? datum orig-env answer @env)
                  (n)
                  (y answer @env n)))))))
       {:rule (assoc (meta the-rule)
                :equiv? equiv?
                :rule-type ::prewalk-simplifier)
        `child-rules (fn [_] [the-rule])
        `recombine (fn [_ rules]
                     (if (next rules)
                       (prewalk-simplifier equiv? walk (rule-list rules))
                       (prewalk-simplifier equiv? walk (first rules))))}))))

(defn rule-simplifier
  "Run a list of rule combinators repeatedly on all subexpressions until running
  them makes no further changes.

  DEPRECATED, use [[simplifier]] instead. This one does not let you set [[equiv?]]."
  [& rules]
  {:deprecated "0.0"}
  (vary-meta
   (simplifier (apply rule-list rules))
   assoc-in [:rule :rule-type] ::rule-simplifier))
