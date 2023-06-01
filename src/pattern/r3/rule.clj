(ns pattern.r3.rule
  (:require [pattern.match.core :refer [run-matcher value-dict compile-pattern]]
            [pattern.match.predicator :refer [*pattern-replace* apply-replacements]])
  (:import (pattern.types Success SuccessEnv SuccessUnmodified)
           (clojure.lang IFn IObj IMeta)))

(def ^:dynamic *debug-rules* false)

(def ^:dynamic *post-processor*
    "Transform the resulting value or env of a successful rule in the context of
  the original value and env.

  Argument and return signature:

  (fn [rule value orig-value env orig-env]
    [value env])

  Set to nil to skip post-processing.

  See also [[*identity-rule-post-processor*]], [[raw]], and others."
  nil)

(def ^:dynamic *identity-rule-post-processor*
  "Transform the resulting value or env of a successful identity rule.

  See [[*post-processor*]] for details.

  The value and orig-value arguments will be identical."
  nil)

(declare match-rule invoke-rule)

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

(defn rule-name
  "Get the name or pattern to identify the rule."
  [rule]
  (let [m (:rule (meta rule))]
    (or (:name m) (:pattern m))))

(defn run-rule
  "Runs a rule and returns either the successfully updated value or the original
  if the rule fails."
  ([rule datum env]
   (rule datum env nil
     (fn rule-succeeded [d e _] [d e])
     (fn rule-failed [] [datum env])))
  ([rule datum events env]
   (rule datum env events
     (fn rule-succeeded [d e _] [d e])
     (fn rule-failed [] [datum env]))))

(deftype Rule [match-procedure handler get-values post-process metadata]
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
    (Rule. match-procedure handler get-values post-process metadata))
  IMeta
  (meta [rule] metadata))


(defmethod print-method Rule [r ^java.io.Writer w]
  (.write w (prn-str
             (list 'rule
                   (:pattern (:rule (meta r)))
                   (:src (:rule (meta r)) '...)))))

(defn- match-rule [^Rule rule data env dict succeed]
  (when env (assert (map? env)))
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

(defn post-process [^Rule rule value orig-value env orig-env]
  (if (instance? Rule rule)
    (if (.post-process rule)
      ((.post-process rule) rule value orig-value env orig-env)
      [value env])
    (throw (ex-info "Not a rule" {:thing rule :meta (meta rule)}))))

(defn invoke-rule [^Rule rule data env {:keys [on-match on-result]} succeed fail]
  (if-let [r (run-matcher (.match-procedure rule) data
                          (fn [dict]
                            (let [r (if on-match
                                      (when-let [[data dict env] (on-match rule env dict)]
                                        (match-rule rule data env dict succeed))
                                      (match-rule rule data env dict succeed))]
                              (if on-result
                                (on-result rule r data dict env)
                                r))))]
    (if (fn? r)
      r ;; this does get hit when using `sub`, but don't recall why.
      (let [[result new-env] r
            new-env (unwrap-env new-env result)
            result (unwrap data result)]
        (post-process rule result data new-env env)))
    (fail)))

(defn dict-handler [match-procedure]
  "Pass this to make-rule as the `->get-values` argument to configure it to call
  the rule handler function with a dictionary of match data when processing a
  match.

  Otherwise use [[pattern.match.core/all-values]] to do named positional
  arguments, or provide your own function."
  (comp list (value-dict match-procedure)))

(defn do-pattern-replace [pattern]
  (apply-replacements pattern *pattern-replace*))

(defn make-rule
  "Compiler for rules. Returns a function that when called with a datum either
  returns the original value or if the pattern matches and the handler returns a
  value, return the value returned by the handler.

  Rules are meant to be combined via the combinators library.

  By default, calls the handler with a simple dictionary of matches - configured
  via the [[dict-handler]] arg transformer -, but a custom arg transformation can
  be specified by providing ->get-values, which is called with the compiled
  match-procedure at compile time, then the result of that is called with the
  results dictionary and applied to the handler.

  Note that the [[rule]] macro enables splicing even in simple quoted rules, but
  that is only possible with a macro. To get the same behaviour with the
  make-rule function directly, either use the [[pattern/quo]] macro to turn spliceable
  syntax quoted lists into regular quoted lists by stripping the namespace from
  all symbols, or use regular syntax-quoted lists."
  ([orig-pattern handler]
   (make-rule orig-pattern handler dict-handler *post-processor* {}))
  ([orig-pattern handler metadata]
   (make-rule orig-pattern handler dict-handler *post-processor* metadata))
  ([orig-pattern handler ->get-values post-process metadata]
   (let [pattern (do-pattern-replace orig-pattern)
         match-procedure (compile-pattern pattern)
         get-values (->get-values match-procedure)]
     (->Rule match-procedure handler get-values post-process
             {:rule
              (merge (meta match-procedure)
                     {:rule-type :pattern/rule
                      :match match-procedure
                      :handler handler}
                     metadata)}))))
