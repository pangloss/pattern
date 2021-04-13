(ns matches.rules
  "This namespace bootstraps the core rule macro and some utility functions."
  (:require [matches.match.core :refer [matcher compile-pattern all-values
                                        run-matcher pattern-names]]
            matches.matchers
            [matches.substitute :refer [substitute]]
            [matches.nanopass.predicator :refer [*pattern-replace* apply-replacements]]
            [clojure.walk :as walk]
            [matches.types :refer [->SuccessUnmodified ->Success]]
            [matches.rule-combinators :refer [*debug-rules* run-rule]])
  (:import (matches.types Success SuccessUnmodified)))

;;;; rule-implementation

(defn success
  "Explicitly mark an object as successfully matched when returned from a rule.

  The rule will unwrap the data automatically.

  Allows rules to return user data directly without failing.

      (success false)  ;; Allows the rule to return false without failing.

  The arity-0 version tells the matcher to use the original input data, also
  discarding any changes made by patterns that may have recursively matched with
  the rule."
  ([] (->SuccessUnmodified))
  ([x] (->Success x)))

(defn- unwrap
  "If a value was marked as (success x), unwraps and returns x."
  [original x]
  (if (instance? Success x)
    (.x ^Success x)
    (if (instance? SuccessUnmodified x)
      original
      x)))

(defn do-pattern-replace [pattern]
  (apply-replacements pattern *pattern-replace*))

(defn make-rule
  "Compiler for rule when called with arity-1 or arity-2."
  [orig-pattern orig-handler]
  (let [pattern (do-pattern-replace orig-pattern)
        match-procedure (compile-pattern pattern)
        handler (bound-fn* orig-handler)]
    (letfn [(match-rule [data succeed]
              (fn in-match-rule [dict]
                (when-let [result (apply handler ((all-values match-procedure) dict))]
                  (when *debug-rules*
                    (prn '>> data)
                    (prn '=> (unwrap data result)))
                  (succeed (or (unwrap data result) result) (constantly false)))))]
      (with-meta
        (fn the-rule
          ([data] (run-rule the-rule data))
          ([data succeed fail]
           (if-let [r (run-matcher match-procedure data (match-rule data succeed))]
             (unwrap data r)
             (fail))))
        {:rule (assoc (meta match-procedure)
                      :builder #'make-rule
                      :build-args [orig-pattern
                                   orig-handler]
                      :rule-type :matches/rule
                      :match match-procedure
                      :match-rule match-rule)}))))

(defn make-sub-rule
  "Compiler for rule when called with arity-3."
  [orig-pattern sub-pattern orig-sub-dict]
  (let [pattern (do-pattern-replace orig-pattern)
        match-procedure (compile-pattern pattern)
        sub-matcher (substitute sub-pattern)
        to-sub-dict (bound-fn* orig-sub-dict)]
    (letfn [(match-rule [data succeed]
              (fn in-match-rule [dict]
                (when-let [sub-dict
                           (apply to-sub-dict
                                  ((all-values match-procedure) dict))]
                  (let [lookup (fn [k default]
                                 (if-let [v (find sub-dict k)]
                                   (val v)
                                   (if-let [v (find dict k)]
                                     (:value (val v))
                                     default)))]
                    (let [result (sub-matcher lookup nil)]
                      (when *debug-rules*
                        (prn '>> data)
                        (prn '=> result))
                      (succeed (or result (success result))
                               (constantly false)))))))]
      (with-meta
        (fn the-rule
          ([data] (run-rule the-rule data))
          ([data succeed fail]
           (if-let [r (run-matcher match-procedure data (match-rule data succeed))]
             (unwrap data r)
             (fail))))
        {:rule (assoc (meta match-procedure)
                      :builder #'make-sub-rule
                      :build-args [orig-pattern
                                   sub-pattern
                                   orig-sub-dict]
                      :rule-type :matches/rule
                      :match match-procedure
                      :match-rule match-rule)}))))

(defn rule-name
  "Attach a rule name to the given object's metadata."
  [name rule]
  (vary-meta rule assoc-in [:rule :name] name))

(defn rule-fn
  "Turn a rule combinator into a simple function of datum -> datum."
  ([rule-combinator]
   (with-meta
     (fn rule-runner [datum]
       (run-rule rule-combinator datum))
     (assoc (meta rule-combinator)
            :combinator rule-combinator)))
  ([rule-combinator datum]
   ((rule-fn rule-combinator) datum)))

(defonce pure-pattern (atom identity))
(defonce spliced (atom identity))
(defonce qsub* (atom nil))

(defmacro sub
  "Use the version in the matches.rewrite namespace."
  [form]
  (if @qsub*
    (rule-fn @qsub* form)
    form))

(defn pattern-args
  "Return the correctly ordered list of variable names in the pattern for use in
  defining a function that may be called with the result of calling all-values
  on a match result.

  This function uses pure-pattern to remove all data from the pattern to prevent
  arg name generation."
  [pattern]
  ;; TODO: is tidying still required? Generate a test that proves the necessity.
  (let [tidied (if (and (seqable? pattern) (= 'quote (first pattern)))
                 (second pattern)
                 (let [pp (@pure-pattern pattern)]
                   (if (= 'identity pp)
                     pattern
                     pp)))]
    (with-redefs [unquote (constantly identity)
                  unquote-splicing (constantly [identity])]
      (vec (pattern-names tidied)))))


(defmacro rule
  "Create a single rule. There are 3 arities, each with unique behavior.

  Arity 1: [pattern] -> identity rule (see below)
  Arity 2: [pattern body] -> simple replacement rule
  Arity 3: [pattern sub-pattern dict] -> replacement by pattern and extended match map

  If the `body` of arity 2 or `dict` of arity 3 are nil/false, the rule fails,
  the same as if it had not matched at all. If the matcher can backtrack and
  make another match, it may attempt tho body/dict expression multiple times.
  Once the expression returns a valid replacement value or map, the rule
  will have matched, the replacement will be made, and no further backtracking
  will happen.

  All pattern variables are bound with the match data in the handler body.
  For instance an arity 2 rule binding ?a and ?b that returns the sum of those
  matches:

      (rule '(?a [?b]) (+ a b))

  Rules may have unquote and spliced unquote in their definitions even if they are
  defined as normal quoted lists. The functionality is provided by a ruleset in
  matches.rewrite/spliced. It allows the following, but note that splices in rule
  definitions only happen at *compile time*:

      (rule '[(? a ~my-pred) ~@my-seq-of-things]
            {:matched a})

  An arity 3 rule specifies 2 patterns, a match pattern and a replacement
  pattern. The third argument must be an expression that either returns a map or
  nil. An example:

      (rule '(?url [?token])
            `(connect ?url ?opts)
            (when token {:opts {:token token}})

  Which may affect the the following transformation:

      (\"url\" [\"x\"]) => (connect \"url\" {:token \"x\"})

  But the (when token...) statement would cause (\"url\" [nil]) not to match.

  A rule with no handler will act as an identity rule, and will always match.
  This may be useful within rule lists or for other higher level rule
  combinators that make use of the rule metadata in the match expression."
  ([pattern]
   `(let [p# ~(@spliced pattern)]
      (make-rule p# (fn ~(pattern-args pattern)
                      (sub ~(if (= 'quote (first pattern))
                               (second pattern)
                               pattern))))))
  ([pattern handler-body]
   `(let [p# ~(@spliced pattern)]
      (make-rule p# (fn ~(pattern-args pattern)
                      ~handler-body))))
  ([pattern sub-pattern to-sub-dict-body]
   `(let [p# ~(@spliced pattern)]
      (make-sub-rule p# ~(@spliced sub-pattern)
                     (fn ~(pattern-args pattern)
                       ~to-sub-dict-body)))))

;; Now that rules can be defined, use the rule engine to enhance itself.
(try
  (require 'matches.rewrite)
  (catch Exception e
    (println "Failed to load matches.rewrite")
    (prn e)))
