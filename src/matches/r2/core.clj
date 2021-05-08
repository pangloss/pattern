(ns matches.r2.core
  "This namespace bootstraps the core rule macro and some utility functions."
  (:require [matches.match.core :refer [matcher compile-pattern all-values
                                        run-matcher pattern-names value-dict]]
            matches.matchers
            [matches.substitute :refer [substitute]]
            [matches.match.predicator :refer [*pattern-replace* apply-replacements]]
            [clojure.walk :as walk]
            [matches.types :refer [->SuccessUnmodified ->Success ->SuccessEnv]]
            [matches.r2.combinators :refer [*debug-rules* run-rule]])
  (:import (matches.types Success SuccessEnv SuccessUnmodified)))

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
  ([x] (->Success x))
  ([x env] (->SuccessEnv x env)))

(defn success:env
  "Success but only change the env."
  [env]
  (success (success) env))

(defn- unwrap
  "If a value was marked as (success x), unwraps and returns x."
  [original x]
  (if (instance? Success x)
    (.x ^Success x)
    (if (instance? SuccessEnv x)
      (unwrap original (.x ^SuccessEnv x))
      (if (instance? SuccessUnmodified x)
        original
        x))))

(defn- unwrap-env [env x]
  (if (instance? SuccessEnv x)
    (.env ^SuccessEnv x)
    env))

(defn do-pattern-replace [pattern]
  (apply-replacements pattern *pattern-replace*))

(defn dict-handler [match-procedure]
  "Pass this to make-rule as the `->get-values` argument to configure it to call
  the rule handler function with a dictionary of match data when processing a
  match.

  Otherwise use [[matches.match.core/all-values]] to do named positional
  arguments, or provide your own function."
  (comp list (value-dict match-procedure)))

(defn make-rule
  "Compiler for rules. Returns a function that when called with a datum either
  returns the original value or if the pattern matches and the handler returns a
  value, return the value returned by the handler.

  Rules are meant to be combined via the combinators library.

  By default, calls the handler with a simple dictionary of matches (configured
  via the [[dict-handler]] arg transformer), but a custom arg transformation can
  be specified by providing ->get-values, which is called with the compiled
  match-procedure at compile time, then the result of that is called with the
  results dictionary and applied to the handler.

  Note that the [[rule]] macro enables splicing even in simple quoted rules, but
  that is only possible with a macro. To get the same behaviour with the
  make-rule function directly, either use the [[matches/quo]] macro to turn spliceable
  syntax quoted lists into regular quoted lists by stripping the namespace from
  all symbols, or use regular syntax-quoted lists."
  ([orig-pattern orig-handler]
   (make-rule orig-pattern orig-handler dict-handler {}))
  ([orig-pattern orig-handler ->get-values metadata]
   (let [pattern (do-pattern-replace orig-pattern)
         match-procedure (compile-pattern pattern)
         handler (bound-fn* orig-handler)
         get-values (->get-values match-procedure)]
     (letfn [(match-rule [data env succeed]
               (fn in-match-rule [dict]
                 (let [env (assoc env :rule/datum data)]
                   (when-let [result (apply handler
                                            env
                                            (get-values dict))]
                     (when *debug-rules*
                       (prn '>> data)
                       (prn '=> (unwrap data result)))
                     (succeed (or (unwrap data result) result)
                              (unwrap-env env result)
                              (constantly false))))))]
       (with-meta
         (fn the-rule
           ([data] (first (run-rule the-rule data nil)))
           ([data env]
            (run-rule the-rule data env))
           ([data env succeed fail]
            (if-let [r (run-matcher match-procedure data
                                    (match-rule data env succeed))]
              (if (fn? r)
                r
                (let [[result env] r]
                  [(unwrap data result) (unwrap-env env result)]))
              (fail))))
         {:rule (merge (assoc (meta match-procedure)
                              :builder #'make-rule
                              :build-args [orig-pattern
                                           orig-handler]
                              :rule-type :matches/rule
                              :match match-procedure
                              :match-rule match-rule)
                       metadata)})))))

(defn rule-name
  "Attach a rule name to the given object's metadata."
  [name rule]
  (vary-meta rule assoc-in [:rule :name] name))

(defonce pure-pattern (atom identity))
(defonce spliced (atom identity))
(defonce qsub* (atom identity))

(defmacro sub
  "Use the version in the matches.r2.rewrite namespace."
  [form]
  (@qsub* form))

(defn pattern-args
  "Return the correctly ordered list of variable names in the pattern for use in
  defining a function that may be called with the result of calling all-values
  on a match result.

  This function uses pure-pattern to remove all data from the pattern to prevent
  arg name generation."
  [pattern]
  (let [tidied (if (and (seqable? pattern) (= 'quote (first pattern)))
                 (second pattern)
                 (let [pp (@pure-pattern pattern)]
                   (if (= 'identity pp)
                     pattern
                     pp)))]
    (with-redefs [unquote (constantly identity)
                  unquote-splicing (constantly [identity])]
      (pattern-names tidied))))

(defn- with-env-args [env-args body]
  (if (seq env-args)
    `(let [~@(mapcat (fn [arg]
                       [arg `(~'%env ~(keyword arg))])
                     env-args)]
       ~body)
    body))

(defn- may-call-success0? [body]
  (boolean (some #{'(success) 'success:env
                   `(success) `success:env}
                 (tree-seq list? seq body))))

(defmacro rule
  "Create a single rule. There are 2 arities, both with unique behavior.

  Arity 1: [pattern] -> identity rule (see below)
  Arity 2: [pattern body] -> simple replacement rule

  If the `body` of arity 2 is nil/false the rule fails the same as if it had not
  matched at all. If the matcher can backtrack and make another match, it may
  attempt tho body/dict expression multiple times.  Once the expression returns
  a valid replacement value or map, the rule will have matched, the replacement
  will be made, and no further backtracking will happen.

  All pattern variables are bound with the match data in the handler body.
  For instance an arity 2 rule binding ?a and ?b that returns the sum of those
  matches:

      (rule '(?a [?b]) (+ a b))

  Rules may have unquote and spliced unquote in their definitions even if they are
  defined as normal quoted lists. The functionality is provided by a ruleset in
  matches.r2.rewrite/spliced. It allows the following, but note that splices in rule
  definitions only happen at *compile time*:

      (rule '[(? a ~my-pred) ~@my-seq-of-things]
            {:matched a})

  A rule with no handler will act as an identity rule, and will always match.
  This may be useful within rule lists or for other higher level rule
  combinators that make use of the rule metadata in the match expression."
  ([pattern]
   (let [args (into ['%env] (pattern-args pattern))]
     `(let [p# ~(@spliced pattern)]
        (make-rule p# (fn ~args
                        (sub ~(if (= 'quote (first pattern))
                                (second pattern)
                                pattern)))
                   all-values {}))))
  ([pattern handler-body]
   (let [args (into ['%env] (pattern-args pattern))]
     `(let [p# ~(@spliced pattern)]
        (make-rule p# (fn ~args
                        ~(with-env-args (:env-args (meta pattern)) handler-body))
                   all-values
                   {:may-call-success0? ~(may-call-success0? handler-body)})))))
