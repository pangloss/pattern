(ns matches.match.predicator
  (:require [clojure.walk :as walk]))

(def ^:dynamic *pattern-replace*
  "Add maps used by postwalk-replace or functions that return a transformed
  pattern here, and they will be applied to each rule pattern with
  [[do-pattern-replace]] before the rule is compiled."
  [])

(defn apply-replacements [pattern replacements]
  (reduce (fn [pattern pr]
            (cond (ifn? pr) (pr pattern)
                  (map? pr) (walk/postwalk-replace pr pattern)
                  :else (throw (ex-info "Unknown *pattern-replace* object"
                                        {:pr pr}))))
          pattern
          replacements))

(defn on-each
  "Mark that a predicate should apply to each element of a sequential matcher.

  Usage:

      (?? x ~(on-each symbol?))"
  [pred]
  (if (instance? clojure.lang.IObj pred)
    (with-meta pred {:each true})
    pred))

(defn var-abbr [prefix n]
  nil
  #_
  (if prefix
    (symbol prefix)
    (when-let [[_ abbr :as x] (re-matches #"[^?\w]*(\w+?)[*+0123456789]*" (name n))]
      (symbol abbr))))

(defn match-abbr [abbr]
  (let [p0 (re-pattern (str "(\\?+)([^?\\w]*)(" (name abbr) ":)([a-zA-Z]\\S*)"))
        p1 (re-pattern (str "(\\?+)([^?\\w]*)()(" (name abbr) "[*+0123456789]*)"))]
    (fn symbol-matcher [x]
      (when (symbol? x)
        (or (re-matches p0 (name x))
            (re-matches p1 (name x)))))))

(defn make-abbr-predicator
  "Create a function that when applied to a pattern, will add the given
  predicate to any short-form var that has the given `abbr` as the main
  component of its name, or if it has a prefix, that matches the prefix.

  Example:

      (make-abbr-predicator 'sym symbol?)

  As applied to various patterns:

      ?sym          => (? sym ~symbol?)
      ?sym*0        => (? sym*0 ~symbol?)
      ??sym         => (?? sym ~symbol?)
      ??->sym+      => (??-> sym+ ~symbol?)
      ?<-$!sym:name => (?<-$! sym:name ~symbol?)

      ;; abbr must match, and matcher must be short-form:
      ?x            => ?x
      (? sym)       => (? sym)

  If `metadata` is provided, it will be attached to the matcher name, and the
  matcher will be marked with a `$` mode character.

      ?sym         => (?$ ~(with-meta 'sym metadata) ~symbol)"
  ([abbr predicate]
   (make-abbr-predicator nil abbr predicate))
  ([metadata abbr predicate]
   (when predicate
     (let [symbol-matcher (match-abbr abbr)
           mode (when metadata "$")]
       (with-meta
         (fn predicator [pattern]
           (walk/postwalk (fn [x]
                            (if-let [[m ? -> p n] (symbol-matcher x)]
                              (list (symbol (str ? -> mode))
                                    (with-meta (symbol (str p n)) metadata)
                                    (if (= "??" ?)
                                      (on-each predicate)
                                      predicate))
                              x))
                          pattern))
         {:predicator {:abbr abbr
                       :predicate predicate
                       :metadata metadata}})))))

(defn with-predicates* [pred-map body-fn]
  (with-bindings* {#'*pattern-replace* (conj (or *pattern-replace* [])
                                             (reduce (fn [f [k v]]
                                                       (comp f (make-abbr-predicator k v)))
                                                     identity
                                                     pred-map))}
    body-fn))

(defmacro with-predicates [pred-map & forms]
  `(with-predicates* ~pred-map (fn [] ~@forms)))
