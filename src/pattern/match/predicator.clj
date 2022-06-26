(ns pattern.match.predicator
  (:require [clojure.walk :as walk]))

(def ^:dynamic *pattern-replace*
  "Add maps used by postwalk-replace or functions that return a transformed
  pattern here, and they will be applied to each rule pattern with
  [[do-pattern-replace]] before the rule is compiled."
  [])

(defn match-abbr [abbr]
  (let [p0 (re-pattern (str "(\\?+)([^?\\w]*)(" (name abbr) ":)([a-zA-Z]\\S*)"))
        p1 (re-pattern (str "(\\?+)([^?\\w]*)()(" (name abbr) "[*+0123456789]*)"))]
    (fn symbol-matcher [x]
      (when (symbol? x)
        (or (re-matches p0 (name x))
            (re-matches p1 (name x)))))))

(defn apply-predicator [{:keys [abbr predicate metadata]} pattern]
  (let [mode (when metadata "$")
        symbol-matcher (match-abbr abbr)]
    (walk/postwalk (fn [x]
                     (if-let [[m ? -> p n] (symbol-matcher x)]
                       (list* (symbol (str ? -> mode))
                              (with-meta (symbol (str p n)) metadata)
                              (when predicate
                                [predicate]))
                       x))
                   pattern)))

(defn apply-replacements [pattern replacements]
  (reduce (fn [pattern pr]
            (cond (:predicator pr)
                  (apply-predicator pr pattern)
                  (ifn? pr) (pr pattern)
                  (map? pr) (walk/postwalk-replace pr pattern)
                  :else (throw (ex-info "Unknown *pattern-replace* object"
                                        {:pr pr}))))
          pattern
          replacements))

(defn var-abbr [prefix n]
  (if prefix
    (symbol prefix)
    (when n
      (when-let [[_ abbr :as x] (re-matches #"[^?\w]*(\w+?)[*+0123456789]*" (name n))]
        (symbol abbr)))))

(defn make-abbr-predicator
  "Create a function that when applied to a pattern, will add the given
  predicate to any short-form var that has the given `abbr` as the main
  component of its name, or if it has a prefix, that matches the prefix.

  Actually just captures the data to build it. The function itself can be built
  on demand and this way it's more inspectable.

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
   (when (or predicate metadata)
     {:predicator true
      :abbr abbr
      :predicate predicate
      :metadata metadata})))

(defn with-predicates* [pred-map body-fn]
  (with-bindings* {#'*pattern-replace* (concat *pattern-replace*
                                               (map (fn [[k v]]
                                                      (make-abbr-predicator k v))
                                                    pred-map))}
    body-fn))

(defmacro with-predicates [pred-map & forms]
  `(with-predicates* ~pred-map (fn [] ~@forms)))
