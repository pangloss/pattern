(ns matches.r3.core
  "This namespace bootstraps the core rule macro and some utility functions."
  (:require [matches.match.core :refer [matcher compile-pattern
                                        run-matcher pattern-names
                                        all-values value-dict]]
            matches.matchers
            [genera.trampoline :refer [bounce?]]
            [matches.substitute :refer [substitute]]
            [matches.match.predicator :refer [*pattern-replace* apply-replacements]]
            [clojure.walk :as walk]
            [matches.types :refer [->SuccessUnmodified ->Success ->SuccessEnv]]
            [matches.r3.combinators :as rc :refer [*debug-rules* run-rule]])
  (:import (matches.types Success SuccessEnv SuccessUnmodified)
           (clojure.lang IFn IObj IMeta)))

(defn raw-matches
  "A success continuation that just returns the match 'dictionary', which may be
  either a dictionary or a function that behaves the same way as calling a map."
  [match-procedure]
  (comp list identity))

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

(declare match-rule invoke-rule)

(deftype Rule [match-procedure handler get-values metadata]
  IFn
  (applyTo [rule args]
    (apply invoke-rule rule args))
  (invoke [rule data]
    (first (run-rule rule data nil)))
  (invoke [rule data env]
    (run-rule rule data env))
  (invoke [rule data env succeed fail]
    (invoke-rule rule data env nil succeed fail))
  (invoke [rule data env events succeed fail]
    (invoke-rule rule data env events succeed fail))

  IObj
  (withMeta [rule metadata]
    (Rule. match-procedure handler get-values metadata))
  IMeta
  (meta [rule] metadata))

(defmethod print-method Rule [r ^java.io.Writer w]
  (.write w (prn-str
             (list 'rule
                   (:pattern (:rule (meta r)))
                   (:src (:rule (meta r)) '...)))))

(defn- match-rule [^Rule rule data env dict succeed]
  (let [env (assoc env :rule/datum data
                   #_#_:match/dict dict)]
    (when-let [result (apply (.handler rule)
                             env
                             ((.get-values rule) dict))]
      (when *debug-rules*
        (prn '>> data)
        (prn '=> (unwrap data result)))
      (succeed (or (unwrap data result) result)
               (unwrap-env env result)
               (constantly false)))))

(defn invoke-rule [^Rule rule data env {:keys [on-match on-result]} succeed fail]
  (if-let [r (run-matcher (.match-procedure rule) data
                          (fn [dict]
                            (let [r (if on-match
                                      (when-let [[data dict env] (on-match rule dict)]
                                        (match-rule rule data env dict succeed))
                                      (match-rule rule data env dict succeed))]
                              (if on-result
                                (on-result rule r data dict env)
                                r))))]
    (if (fn? r)
      r
      (let [[result env] r]
        [(unwrap data result) (unwrap-env env result)]))
    (fail)))


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
     (->Rule match-procedure handler get-values
             {:rule
              (merge (meta match-procedure)
                     {:rule-type :matches/rule
                      :match match-procedure
                      :handler handler}
                     metadata)}))))

(reset! rc/make-rule #'make-rule)

(defn rule-name
  "Attach a rule name to the given object's metadata."
  [name rule]
  (vary-meta rule assoc-in [:rule :name] name))

(defonce pure-pattern (atom identity))
(defonce spliced (atom identity))
(defonce qsub* (atom identity))
(defonce rule-src (atom identity))

(defmacro sub
  "Use the version in the matches.r3.rewrite namespace."
  [form]
  (@qsub* form))

(defn pattern-args
  "Return the correctly ordered list of variable names in the pattern for use in
  defining a function that may be called with the result of calling all-values
  on a match result.

  This function uses pure-pattern to remove all data from the pattern to prevent
  arg name generation.

  This is so complex is because this function is designed to be called during
  macro expansion. It must eliminate any non-pattern expressions because they
  could look like matchers and be included in the list of matcher names, which
  would cause an arity error when the matcher is called. The identity function
  was chosen arbitrarily to replace all expressions because it could appear in the
  (? x identity) position, so needs to resolve as a function when the var is
  resolved."
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

(defn- extract-args [matches args]
  (when (seq args)
    (mapcat (fn [arg]
              [arg `(get (~matches '~arg) :value)])
            args)))

(defn- env-args [env-args]
  (when (seq env-args)
    (mapcat (fn [arg]
              [(symbol (name arg)) `(~'%env ~(keyword arg))])
            env-args)))

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
  matches.r3.rewrite/spliced. It allows the following, but note that splices in rule
  definitions only happen at *compile time*:

      (rule '[(? a ~my-pred) ~@my-seq-of-things]
            {:matched a})

  A rule with no handler will act as an identity rule, and will always match.
  This may be useful within rule lists or for other higher level rule
  combinators that make use of the rule metadata in the match expression."
  ([pattern]
   (let [args (pattern-args pattern)
         matches (gensym 'matches)]
     `(let [p# ~(@spliced pattern)]
        (make-rule p# (fn [env# ~matches] (success))
                   raw-matches {:may-call-success0? true
                                :src '(success)}))))
  ([pattern handler-body]
   (let [args (pattern-args pattern)
         matches (gensym 'matches)]
     `(let [p# ~(@spliced pattern)]
        (make-rule p# (fn [~'%env ~matches]
                        ;; TODO: should env-args or regular args dominate? or should a conflict be an error?
                        ;; TODO: is the JVM smart about eliding unused bindings here or should I try
                        ;;       to introspect the body to determine which args are used?
                        (let [~@(extract-args matches args)
                              ~@(env-args (:env-args (meta pattern)))]
                          ~handler-body))
                   raw-matches
                   {:may-call-success0? ~(may-call-success0? handler-body)
                    :src '~handler-body})))))
