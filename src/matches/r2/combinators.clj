(ns matches.r2.combinators
  (:refer-clojure :exclude [trampoline])
  (:require [matches.match.core :refer [run-matcher]]
            [matches.substitute :refer [substitute]]
            [clojure.string :as str]
            [genera :refer [trampoline bouncing]]
            [clojure.walk :as walk]))

(def ^:dynamic *debug-rules* false)

(defn run-rule
  "Runs a rule and returns either the successfully updated value or the original
  if the rule fails."
  [rule datum env]
  (rule datum env (fn [d e _] [d e]) (fn [] [datum env])))

(defn rule-list [& rules]
  (let [rules (flatten rules)]
    (with-meta
      (fn do-rule-list
        ([data] (first (run-rule do-rule-list data nil)))
        ([data env] (run-rule do-rule-list data env))
        ([data env succeed fail]
         (letfn [(per-rule [[r :as rules]]
                   (when (and *debug-rules* r) (prn 'try (:pattern (:rule (meta r)))))
                   (if (seq rules)
                     (r data env succeed
                        #(bouncing (per-rule (rest rules))))
                     (fail)))]
           (trampoline per-rule rules))))
      {:rule {:rule-type ::rule-list
              :rules (vec
                      (mapcat (fn [rule]
                                (let [m (meta rule)]
                                  (if (= ::rule-list (:rule-type (:rule m)))
                                    (:rules (:rule m))
                                    [m])))
                              rules))}})))

(defn in-order [rules]
  (let [rc (count rules)]
    (letfn [(per-rule [datum env [r :as rules] n]
              (when *debug-rules* (println (str "#" (inc n) "/" rc " try" (:pattern (:rule (meta r))))))
              (if (seq rules)
                (r datum
                   env
                   (fn [result env _]
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " succeded")))
                     (bouncing (per-rule (if (= datum result)
                                           datum result)
                                         env
                                         (next rules) (inc n))))
                   (fn []
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " failed")))
                     (bouncing (per-rule datum env (next rules) (int n)))))
                (do
                  (when *debug-rules* (println (str "#" (inc n) "/" rc " ran out of rules")))
                  [datum env])))]

      (with-meta
        (fn do-in-order
          ([data] (first (run-rule do-in-order data nil)))
          ([data env] (run-rule do-in-order data env))
          ([orig-datum orig-env succeed fail]
           (let [[result env] (trampoline per-rule orig-datum orig-env rules 0)]
             (if (and (= orig-datum result) (= orig-env env))
               (fail)
               (succeed result env fail)))))
        {:rule {:rule-type ::in-order
                :rules (mapv meta rules)}}))))

(defn guard [f rule]
  (with-meta
    (fn do-predicate
      ([data] (first (run-rule do-predicate data nil)))
      ([data env] (run-rule do-predicate data env))
      ([datum env succeed fail]
       (if (f datum env)
         (rule datum env succeed fail)
         (fail))))
    {:rule {:rule-type ::guard
            :predicate f
            :rule rule}}))

(defn n-times [n rule]
  (vary-meta
   (in-order (repeat n rule))
   assoc-in [:rule :rule-type] ::n-times))

(def ^:dynamic *descend* identity)

(defn descend
  "If passing in an env, pass it as the first arg since within a rule handler,
  the expression part is likely to be a large hairy expression, and the env
  aspect will be easily lost at the end of it. "
  ([expression]
   ;; should not bounce through descend, so don't need to check for a function passing through.
   (first (*descend* expression nil)))
  ([expression env]
   (*descend* expression env)))

(def ^:dynamic *descent-depth* nil)
(def ^:dynamic *do-mutual-descent* nil)

(defn- directed:extend-rule-metadata [rule-meta]
  (when-not (= :matches/rule (:rule-type rule-meta))
    (prn rule-meta)
    (prn (:rule-type rule-meta))
    (assert (= :matches/rule (:rule-type rule-meta))))
  (letfn [(detect-mode [rule-meta mode-type mode-string data]
            ;; capture a list of var names with the given mode-type
            (assoc rule-meta mode-type
                   (reduce-kv (fn [m n modes]
                                (if (and modes (str/includes? modes mode-string))
                                  (assoc m n (data n))
                                  m))
                              {} (:var-modes rule-meta))))]
    (let [r (-> rule-meta
                ;; marked with -> for descent.
                (detect-mode :descending? "->" identity)
                ;; marked with $ for mutual recursion.
                (detect-mode :mutual? "$" meta)
                ;; marked with >- for calling a provided function.
                (detect-mode :transform? ">-" identity))

          ;; I'm assuming that descent order does not need to be defined
          ;; (if it needs to be, do something around here...)
          r (assoc r :active (set (concat (keys (:descending? r))
                                          (keys (:transform? r)))))]
      (cond-> r
        ;; If the datum will change after the initial match, and it's possible
        ;; that (success) arity 0 will be called, the datum needs to have the
        ;; new values substituted into it:
        (and (:may-call-success0? r)
             (seq (:active r)))
        (assoc :substitute (substitute (:pattern rule-meta)))))))


(defn- directed:descend-marked [apply-rules f {:keys [active descending? mutual? transform?]} dict env depth]
  (let [apply-rules (partial apply-rules (inc depth))
        mutual-fn *do-mutual-descent*]
    (binding [*descend* apply-rules] ;; TODO: bind descend in do-mutual-descent, too
      (reduce (fn [[dict env] k]
                (if-let [match (dict k)]
                  (let [enter (cond (descending? k) apply-rules
                                    (and mutual-fn (mutual? k))
                                    (partial mutual-fn (mutual? k) (inc depth))
                                    :else vector)
                        enter (if (transform? k)
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
                        [(assoc-in dict [k :value] v) env])
                      (let [[v env] (enter (:value match) env)]
                        [(assoc-in dict [k :value] v) env])))
                  [dict env]))
              [dict env] active))))

(defn directed
  "Recurs depth-first, but only into marked subexpressions.

  Marking a subexpression looks like ?->x or ??->x (ie. marked with -> matcher
  mode), so a matcher like ?y would not get recurred into.

  If subexpressions are marked with >-, the expression or the result of
  traversing into the expression if it is also marked with -> will be passed to
  the function f. If no function is provided, [[identity]] is used. In this case,
  the matcher would look like one of ?>-, ??>-, ?>-> (note this is a shortened
  form), ?>-->, ??->>-, etc. The order of >- and -> does not matter.

  Does not iteratively descend into any expressions returned by matchers. To do
  any iterative descent, call `descend` within the handler on the subexpressions
  you wish to descend into.

  This uses the rule metadata to reconstruct the rules, and does not actually
  run the rule-list or any rules directly

  Note that descent order within expressions is not defined."
  ([rule-list]
   (directed identity rule-list))
  ([f rule-list]
   (let [rules (->> (:rules (:rule (meta rule-list)))
                    (mapv (comp directed:extend-rule-metadata :rule)))]
     ;; some thought would have to go into supporting anything more than simple
     ;; rules in the rule list.
     (assert (= ::rule-list (:rule-type (:rule (meta rule-list)))))
     (with-meta
       (fn do-on-marked
         ([data] (first (run-rule do-on-marked data nil)))
         ([data env] (run-rule do-on-marked data env))
         ([orig-datum orig-env y n]
          (letfn [(apply-rules [depth datum env]
                    (when *debug-rules* (prn (symbol (apply str (repeat depth " "))) '=== datum))
                    (loop [[rule-meta & rules* :as rules] rules
                           datum datum
                           env env]
                      (when (and *debug-rules* rule-meta) (prn (symbol (apply str (repeat depth " ")))
                                                               'try (:pattern rule-meta)))
                      (if (seq rules)
                        (let [{:keys [match match-rule]} rule-meta
                              match-dict (run-matcher match datum identity)]
                          (if match-dict
                            ;; match-rule returns the matcher handler function that takes
                            (let [[match-dict env] (directed:descend-marked apply-rules f rule-meta
                                                                            match-dict env depth)
                                  datum (if-let [s (:substitute rule-meta)]
                                          (s (fn [k none] (:value (match-dict k) none)) nil)
                                          datum)
                                  get-rule-result (match-rule datum env (fn [d env _] [d env]))]
                              (get-rule-result match-dict))
                            (recur rules* datum env)))
                        [datum env])))]
            (binding [*descend* (partial apply-rules (inc (or *descent-depth* 0)))]
              (let [[result env] (apply-rules (or *descent-depth* 0) orig-datum orig-env)]
                (if (and (= orig-datum result) (= orig-env env))
                  (n)
                  (y result env n)))))))
       (assoc-in (meta rule-list)
                 [:rule :rule-type] ::on-marked-subexpressions)))))

(defn on-mutual
  "The idea is that you can create a group of named rule sets where matchers are tagged with metadata and a matcher mode
  that tells this system to switch which rule set is applied for subexpressions of the given type. Effectively this lets you
  switch between expression types (or dialects?) when applying rules to an expression.

  This is currently done in a somewhat simplistic way with bound variables because I'm not exactly sure how it should be structured but
  eventually it should be done without the need for extra global state like this.
  "
  [initial-form name-rule-pairs]
  (let [forms (if (map? name-rule-pairs)
                name-rule-pairs
                (apply hash-map name-rule-pairs))]
    (letfn [(switch-branch [{:keys [form-name]} depth datum env]
              (let [form-name (if (vector? form-name) (second form-name) form-name)
                    rule (forms form-name)]
                ;; TODO: probably want to just keep on the same branch if there is no option? Or maybe don't descend?
                (if rule
                  (binding [*descent-depth* depth]
                    (run-rule rule datum env))
                  [datum env])))]
      (with-meta
        (fn do-mutual
          ([data] (first (run-rule do-mutual data nil)))
          ([data env] (run-rule do-mutual data env))
          ([orig-datum orig-env y n]
           (binding [*do-mutual-descent* switch-branch]
             (let [[result env] (switch-branch {:form-name initial-form} 0 orig-datum orig-env)]
               (if (and (= orig-datum result) (= orig-env env))
                 (n)
                 (y result env n))))))
        {:rule {:rule-type ::on-mutual
                :initial-form initial-form
                :name-rule-pairs (walk/postwalk (some-fn meta identity) name-rule-pairs)}}))))

(defn- try-subexpressions [the-rule datum env]
  (if (and (seqable? datum) (not (string? datum)))
    (let [[result env] (reduce (fn [[result env] d]
                                 (let [[r env] (run-rule the-rule d env)]
                                   [(conj result r) env]))
                               [(empty datum) env] datum)
          result (if (list? result) (reverse result) result)]
      [(if (= result datum)
         datum
         result)
       env])
    [datum env]))


(defn on-subexpressions
  "Run the given rule combinator on all subexpressions depth-first."
  [the-rule]
  (with-meta
    (fn enter-iter-on-subexpr
      ([data] (first (run-rule enter-iter-on-subexpr data nil)))
      ([data env] (run-rule enter-iter-on-subexpr data env))
      ([datum orig-env y n]
       (letfn [(on-expr [datum env on-result fail]
                 (let [[done env] (try-subexpressions on-expr datum env)
                       [answer env] (run-rule the-rule done env)]
                   (if (= done answer)
                     (on-result done env fail)
                     (on-result answer env fail))))]
         (let [[done env] (run-rule on-expr datum orig-env)]
           (if (and (= done datum) (= orig-env env))
             (n)
             (y done env n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::on-subexpressions)}))

(defn iterated
  "Run the given rule combinator repeatedly until running the rule makes no
  further changes."
  [the-rule]
  (with-meta
    (fn do-iter
      ([data] (first (run-rule do-iter data nil)))
      ([data env] (run-rule do-iter data env))
      ([datum orig-env y n]
       (letfn [(iterating [datum env on-result f]
                 (let [[answer env] (run-rule the-rule datum env)]
                   (if (= datum answer)
                     (on-result datum env f)
                     (recur answer env on-result f))))]
         (let [[done env] (run-rule iterating datum orig-env)]
           (if (and (= done datum) (= orig-env env))
             (n)
             (y done env n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::iterated)}))

(defn simplifier
  "Run the given rule combinator repeatedly depth-first on all subexpressions
  until running the rule makes no further changes at each level.

  See also [[rule-simplifer]]."
  [the-rule]
  (with-meta
    (fn enter-iter-on-subexpr
      ([data] (first (run-rule enter-iter-on-subexpr data nil)))
      ([data env] (run-rule enter-iter-on-subexpr data env))
      ([datum orig-env y n]
       (letfn [(on-expr [datum env on-result f]
                 (let [[done env] (try-subexpressions on-expr datum env)
                       [answer env] (run-rule the-rule done env)]
                   (if (= done answer)
                     (on-result done env f)
                     (on-expr answer env on-result f))))]
         (let [[done env] (run-rule on-expr datum orig-env)]
           (if (and (= done datum) (= orig-env env))
             (n)
             (y done env n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::simplifier)}))

(defn rule-simplifier
  "Run a list of rule combinators repeatedly on all subexpressions until running
  them makes no further changes."
  [rules]
  (vary-meta
   (simplifier (rule-list rules))
   assoc-in [:rule :rule-type] ::rule-simplifier))
