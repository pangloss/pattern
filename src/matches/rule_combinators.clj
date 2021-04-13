(ns matches.rule-combinators
  (:refer-clojure :exclude [trampoline])
  (:require [matches.match.core :refer [run-matcher]]
            [clojure.string :as str]
            [uncomplicate.fluokitten.core :as f :refer [fmap]]
            [genera :refer [trampoline bouncing]]
            [clojure.walk :as walk]))

(def ^:dynamic *debug-rules* false)

(defn run-rule
  "Runs a rule and returns either the successfully updated value or the original
  if the rule fails."
  [rule datum]
  (rule datum (fn [d _] d) (fn [] datum)))

(defn rule-list [& rules]
  (let [rules (flatten rules)]
    (with-meta
      (fn do-rule-list
        ([data] (run-rule do-rule-list data))
        ([data succeed fail]
         (letfn [(per-rule [[r :as rules]]
                   (when (and *debug-rules* r) (prn 'try (:pattern (:rule (meta r)))))
                   (if (seq rules)
                     (r data succeed
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
    (letfn [(per-rule [datum [r :as rules] n]
              (when *debug-rules* (println (str "#" (inc n) "/" rc " try" (:pattern (:rule (meta r))))))
              (if (seq rules)
                (r datum
                   (fn [result _]
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " succeded")))
                     (bouncing (per-rule (if (= datum result)
                                           datum result)
                                         (next rules) (inc n))))
                   (fn []
                     (when *debug-rules* (println (str "#" (inc n) "/" rc " failed")))
                     (bouncing (per-rule datum (next rules) (int n)))))
                (do
                  (when *debug-rules* (println (str "#" (inc n) "/" rc " ran out of rules")))
                  datum)))]

      (with-meta
        (fn do-in-order
          ([data] (run-rule do-in-order data))
          ([orig-datum succeed fail]
           (let [result (trampoline per-rule orig-datum rules 0)]
             (if (= orig-datum result)
               (fail)
               (succeed result fail)))))
        {:rule {:rule-type ::in-order
                :rules (mapv meta rules)}}))))

(defn guard [f rule]
  (with-meta
    (fn do-predicate
      ([data] (run-rule do-predicate data))
      ([datum succeed fail]
       (if (f datum)
         (rule datum succeed fail)
         (fail))))
    {:rule {:rule-type ::guard
            :predicate f
            :rule rule}}))

(defn n-times [n rule]
  (vary-meta
   (in-order (repeat n rule))
   assoc-in [:rule :rule-type] ::n-times))

(defn- try-subexpressions [the-rule datum]
  (if (and (seqable? datum) (not (string? datum)))
    (let [result (fmap (partial run-rule the-rule) datum)]
      (if (= result datum)
        datum
        result))
    datum))

(def ^:dynamic *descend* identity)

(defn descend [expression]
  (*descend* expression))

(comment
  (require '[matches.nanopass.predicator :refer [*pattern-replace* make-abbr-predicator]])
  (binding [*do-mutual-descent* (fn [{:keys [form-name]} depth d]
                                  [form-name d])
            *pattern-replace* [(make-abbr-predicator {:form-name 'Thing} 't some?)]]
    (str
     (run-rule
      (directed (rule-list [(matches.rules/rule '[?a ?->t]
                                                {:a a :t t})]))
      '[A B])))

  ;; So, this is something like what needs to be generated:
  (binding [*pattern-replace* [(make-abbr-predicator {:form-name 'Thing} 't symbol?)
                               (make-abbr-predicator {:form-name 'Lambda} 'fn list?)]]
    ((comp meta :t)
     (run-rule
      (on-mutual 'Expr
                 ['Thing (matches.rules/rule '?x "thiiiing!")
                  'Lambda (matches.rules/rule '(fn [??x] ??y)
                                              (with-meta
                                                (matches.rewrite/qsub (lambda ~(reduce (fn [m arg] (assoc m arg nil)) {} x)
                                                                              [??x]
                                                                              (begin ??y)))
                                                {:form-name 'Lambda}))
                  'Expr (on-marked-subexpressions
                         (rule-list [(matches.rules/rule '[?->t:a ?->fn]
                                                         {:a a :t fn})
                                     (matches.rules/rule '(fn [??x] ??y) "oops!")]))])
      '[X (fn [X Y Z] B C)])))

  ;; FIXME: my nice pattern replace rules are not bound in place when the rule
  ;; macro expands, so var names are wrong.
  ;; Meaning instead of `a`, the variable is `t:a`... ouch.
  ;;
  ;; There are 2 easy solutions: names always are the value after the : if
  ;; there is one, or the predicator keeps the whole name including the :.
  ;; I chose the first solution

  ,)

(def ^:dynamic *descent-depth* nil)
(def ^:dynamic *do-mutual-descent* nil)

(defn- directed:extend-rule-metadata [rule-meta]
  (when-not (= :matches/rule (:rule-type rule-meta))
    (prn rule-meta)
    (prn (:rule-type rule-meta))
    (assert (= :matches/rule (:rule-type rule-meta))))
  (-> rule-meta
      ;; capture a list of var names marked with -> for descent.
      (assoc :descending
             (reduce-kv (fn [v n modes]
                          (if (and modes (str/includes? modes "->"))
                            (conj (or v []) n)
                            v))
                        nil (:var-modes rule-meta)))
      ;; capture a list of var names marked with $ for mutual recursion.
      (assoc :mutual
             (reduce-kv (fn [m n modes]
                          (if (and modes (str/includes? modes "$"))
                            (assoc m n (meta n))
                            m))
                        nil (:var-modes rule-meta)))))

(defn- directed:descend-marked [apply-rules {:keys [descending mutual]} dict depth]
  (let [enter (partial apply-rules (inc depth))]
    (binding [*descend* enter] ;; TODO: bind descend in do-mutual-descent, too
      (reduce (fn [dict k]
                (if-let [match (dict k)]
                  (let [enter (if (and *do-mutual-descent* (mutual k))
                                (partial *do-mutual-descent* (mutual k) (inc depth))
                                enter)]
                    (if (#{'?? '?:*} (:type match))
                      ;; TODO: metadata could capture sequence nesting level, which
                      ;; would make this more powerful. Now it only supports 1
                      ;; level of nesting, so some patterns are not correctly
                      ;; represented.
                      (assoc-in dict [k :value] (mapv enter (:value match)))
                      (assoc-in dict [k :value] (enter (:value match)))))
                  dict))
              dict descending))))

(defn directed
  "Recurs depth-first, but only into marked subexpressions.

  Marking a subexpression looks like ?->x or ??->x (ie. marked with -> matcher mode), so
  a matcher like ?y would not get recurred into.

  Does not iteratively descend into any expressions returned by matchers. To do
  any iterative descent, call `descend` within the handler on the subexpressions
  you wish to descend into.

  This uses the rule metadata to reconstruct the rules, and does not actually
  run the rule-list or any rules directly"
  [rule-list]
  (let [rules (->> (:rules (:rule (meta rule-list)))
                   (mapv (comp directed:extend-rule-metadata :rule)))]
    ;; some thought would have to go into supporting anything more than simple
    ;; rules in the rule list.
    (assert (= ::rule-list (:rule-type (:rule (meta rule-list)))))
    (with-meta
      (fn do-on-marked
        ([data] (run-rule do-on-marked data))
        ([orig-datum y n]
         (letfn [(apply-rules [depth datum]
                   (when *debug-rules* (prn (symbol (apply str (repeat depth " "))) '=== datum))
                   (loop [[rule-meta & rules* :as rules] rules
                          datum datum]
                     (when (and *debug-rules* rule-meta) (prn (symbol (apply str (repeat depth " ")))
                                                              'try (:pattern rule-meta)))
                     (if (seq rules)
                       (let [{:keys [match match-rule]} rule-meta
                             dict (run-matcher match datum identity)]
                         (if dict
                           ;; match-rule returns the matcher handler that takes
                           ;; function that takes [data succed fail dict]
                           (let [get-rule-result (match-rule datum (fn [d _] d))
                                 dict (directed:descend-marked apply-rules rule-meta dict depth)]
                             (get-rule-result dict))
                           (recur rules* datum)))
                       datum)))]

           (binding [*descend* (partial apply-rules (inc (or *descent-depth* 0)))]
             (let [datum (apply-rules (or *descent-depth* 0) orig-datum)]
               (if (= datum orig-datum)
                 (n)
                 (y datum n)))))))
      (assoc-in (meta rule-list)
                [:rule :rule-type] ::on-marked-subexpressions))))

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
    (letfn [(switch-branch [{:keys [form-name]} depth datum]
              (let [form-name (if (vector? form-name) (second form-name) form-name)
                    rule (forms form-name)]
                ;; TODO: probably want to just keep on the same branch if there is no option? Or maybe don't descend?
                (if rule
                  (binding [*descent-depth* depth]
                    (run-rule rule datum))
                  datum)))]
      (with-meta
        (fn do-mutual
          ([data] (run-rule do-mutual data))
          ([orig-datum y n]
           (binding [*do-mutual-descent* switch-branch]
             (let [result (switch-branch {:form-name initial-form} 0 orig-datum)]
               (if (= orig-datum result)
                 (n)
                 (y result n))))))
        {:rule {:rule-type ::on-mutual
                :initial-form initial-form
                :name-rule-pairs (walk/postwalk (some-fn meta identity) name-rule-pairs)}}))))

(defn on-subexpressions
  "Run the given rule combinator on all subexpressions depth-first."
  [the-rule]
  (with-meta
    (fn enter-iter-on-subexpr
      ([data] (run-rule enter-iter-on-subexpr data))
      ([datum y n]
       (letfn [(on-expr [datum on-result f]
                 (let [done (try-subexpressions on-expr datum)
                       answer (run-rule the-rule done)]
                   (if (= done answer)
                     (on-result done f)
                     (on-result answer f))))]
         (let [done (run-rule on-expr datum)]
           (if (= done datum)
             (n)
             (y done n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::on-subexpressions)}))

(defn iterated
  "Run the given rule combinator repeatedly until running the rule makes no
  further changes."
  [the-rule]
  (with-meta
    (fn do-iter
      ([data] (run-rule do-iter data))
      ([datum y n]
       (letfn [(iterating [datum on-result f]
                 (let [answer (run-rule the-rule datum)]
                   (if (= datum answer)
                     (on-result datum f)
                     (recur answer on-result f))))]
         (let [done (run-rule iterating datum)]
           (if (= done datum)
             (n)
             (y done n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::iterated)}))



(defn iterated-on-subexpressions
  "Run the given rule combinator repeatedly depth-first on all subexpressions
  until running the rule makes no further changes at each level."
  [the-rule]
  (with-meta
    (fn enter-iter-on-subexpr
      ([data] (run-rule enter-iter-on-subexpr data))
      ([datum y n]
       (letfn [(on-expr [datum on-result f]
                 (let [done (try-subexpressions on-expr datum)
                       answer (run-rule the-rule done)]
                   (if (= done answer)
                     (on-result done f)
                     (on-expr answer on-result f))))]
         (let [done (run-rule on-expr datum)]
           (if (= done datum)
             (n)
             (y done n))))))
    {:rule (assoc (meta the-rule)
                  :rule-type ::iterated-on-subexpressions)}))

(defn rule-simplifier
  "Run a list of rule combinators repeatedly on all subexpressions until running
  them makes no further changes."
  [rules]
  (vary-meta
   (iterated-on-subexpressions (rule-list rules))
   assoc-in [:rule :rule-type] ::rule-simplifier))
