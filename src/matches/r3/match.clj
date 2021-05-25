(ns matches.r3.match
  (:require [matches.r3.combinators :refer [directed rule-list]]
            [matches.r3.core :refer [rule]]))

(defmacro match*
  "Produce a directed rule-list combinator from a flattened list of
  pattern-handler pairs."
  [& pairs]
  `(directed (rule-list ~(mapv (fn [[pattern handler]]
                                 `(rule ~pattern ~handler))
                               (partition 2 pairs)))))

(defmacro match!
  "Create an inline matcher in the typical style. If it doesn't match it will
  raise a restartable condition."
  [datum & pairs]
  `((match* ~@pairs
            ?_ (throw (ex-info "No match" ~'%env)))
    ~datum))

(defmacro match
  "Create an inline matcher in the typical style."
  [datum & pairs]
  `((match* ~@pairs) ~datum))
