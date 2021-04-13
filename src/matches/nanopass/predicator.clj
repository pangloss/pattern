(ns matches.nanopass.predicator
  (:require [clojure.walk :as walk]))

;; TODO: rename to matches.match.predicator

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

(defn per-element [pred]
  (if (instance? clojure.lang.IObj pred)
    (with-meta pred {:per-element true})
    pred))

(defn match-abbr [abbr]
  (let [p0 (re-pattern (str "(\\?+)([^?\\w]*)" (name abbr) ":([a-zA-Z]\\S*)"))
        p1 (re-pattern (str "(\\?+)([^?\\w]*)(" (name abbr) "[*+0123456789]*)"))]
    (fn symbol-matcher [x]
      (when (symbol? x)
        (or (re-matches p0 (name x))
            (re-matches p1 (name x)))))))


(defn make-abbr-predicator
  ([abbr predicate]
   (make-abbr-predicator nil abbr predicate))
  ([metadata abbr predicate]
   (when predicate
     (let [symbol-matcher (match-abbr abbr)
           mode (when metadata "$")]
       (with-meta
         (fn predicator [pattern]
           (walk/postwalk (fn [x]
                            (if-let [[m ? -> n] (symbol-matcher x)]
                              (list (symbol (str ? -> mode))
                                    (with-meta (symbol n) metadata)
                                    (if (= "??" ?)
                                      (per-element predicate)
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
