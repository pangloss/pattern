(ns pattern.types
  (:require [clojure.pprint :refer [simple-dispatch]])
  (:import (clojure.lang IObj IMeta)))

(defrecord Success [x])
(defrecord SuccessEnv [x env])
(defrecord SuccessUnmodified [])
(defrecord ValuesBox [value])
(defrecord MetaBox [value])

;; var-path is the current scope... this design could use a refactoring pass
;; since it wasn't 100% clear when I started building it.
(defrecord Env [succeed
                var-path
                scopes
                scope-path
                lookup
                store
                repetition
                tails])

(declare ->Length)

(defn length-op
  "Defines how to combine multiple length objects.

  Add together minimum lengths and result is variable length if any is variable
  length."
  ([]
   (->Length 0 false))
  ([x]
   x)
  ([x y]
   (->Length (+ (:n x) (:n y)) (or (:v x) (:v y))))
  ([x y & zs]
   (let [all (into [x y] zs)]
     (->Length (apply + (map :n all))
               (reduce (fn [a b] (or a b))
                       (map :v all))))))

(defrecord Length [n v]
  uncomplicate.fluokitten.protocols/Magma
  (op [_] length-op))

(defprotocol RuleCombinator
  :extend-via-metadata true
  (child-rules [rc])
  (recombine [rc rules]))

(defprotocol SpliceablePattern
  :extend-via-metadata true
  (spliceable-pattern [pattern]))

(defn rule-combinator? [r]
  (or (satisfies? RuleCombinator r)
    (let [m (meta r)]
      (or (`child-rules m)
        (`recombine m)))))

(deftype Ok []
  Object
  (equals [a b]
    (instance? Ok b)))

(defmethod print-method Ok [_ ^java.io.Writer w]
  (.write w "ok"))

(defn ok? [x]
  (instance? Ok x))

(def ok (->Ok))

(defmethod simple-dispatch Ok [ok]
  (print-method ok *out*))

(defn obj? [x]
  (instance? IObj x))

(defn meta? [x]
  (instance? IMeta x))

(defn not-meta? [x]
  (not (meta? x)))
