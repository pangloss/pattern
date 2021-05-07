(ns genera.macros
  (:require [genera.core :as c]
            [clojure.core.memoize :as memo]))

(defmacro defgenera [name arity & fn-tail]
  (let [[doc & fn-tail] (if (string? (first fn-tail))
                          fn-tail
                          (cons nil fn-tail))]
    `(do (def ~name (c/generic-procedure-constructor '~name ~arity (fn ~name ~@fn-tail)))
         (alter-meta! (var ~name) merge {:doc ~doc :arglists (list '~(first fn-tail))})
         (var ~name))))

(defmacro defgenera*
  ([name arity default-handler]
   `(defgenera* ~name ~arity nil ~default-handler))
  ([name arity doc default-handler]
   `(let [handler# ~default-handler]
      (def ~name (c/generic-procedure-constructor '~name ~arity handler#))
      (alter-meta! (var ~name) merge {:doc ~doc
                                      ;; a bunch of work to try to produce a nice arglist
                                      :arglists
                                      (filter #(= ~arity (count %))
                                              (or ~(when (symbol? default-handler)
                                                     `(:arglists (meta (var ~default-handler))))
                                                  (:arglists (meta ~default-handler))
                                                  ['~(vec (repeat arity '_))]))})

      (var ~name))))

(defmacro defgenera=
  ([name arity default-value]
   `(defgenera= ~name ~arity nil ~default-value))
  ([name arity doc default-value]
   `(defgenera* ~name ~arity ~doc (constantly ~default-value))))

(defmacro defgen [generic handlers & fn-tail]
  `(c/assign-handler! ~generic (fn ~(symbol (name generic)) ~@fn-tail) ~@handlers))

(defmacro defgen* [generic handlers fn]
  `(c/assign-handler! ~generic ~fn ~@handlers))

(defmacro defgen! [generic handlers fn]
  `(c/assign-handler! ~generic (memo/lru ~fn :lru/threshold 1024) ~@handlers))

(defmacro defgen= [generic handlers const]
  `(c/assign-handler! ~generic (constantly ~const) ~@handlers))

(defmacro defmethod* [multifn dispatch-val fn]
  `(. ~multifn clojure.core/addMethod ~dispatch-val ~fn))

(defmacro defmethod! [multifn dispatch-val fn]
  `(. ~multifn clojure.core/addMethod ~dispatch-val (memo/lru ~fn :lru/threshold 1024)))

(defmacro defmethod= [multifn dispatch-val value]
  `(. ~multifn clojure.core/addMethod ~dispatch-val (constantly ~value)))
