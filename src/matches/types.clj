(ns matches.types)

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
                repetition])

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
