(ns matches.substitute
  "This namespace implements a data-driven substitution system. It's flexible
  but much slower than the one defined in the [[matches.r3.rewrite]] namespace that fully
  precompiles the substitution."
  (:require [matches.match.core :refer [var-name matcher-type-for-dispatch pattern-names *disable-modes* resolve-fn]]
            [genera :refer [defmethod* defmethod!]]))

;; My pattern substitution combinator

(def ^:dynamic *disable-sub-type* #{})
(def ^:dynamic *simple-matchers-only* false)

(defn- matcher-type-for-sub [pattern]
  (let [t (matcher-type-for-dispatch pattern)]
    (if (or (*disable-sub-type* t)
            (and *simple-matchers-only*
                 (not (symbol? pattern))))
      (if (list? pattern)
        :list
        :value)
      t)))

(defmulti sub* matcher-type-for-sub)

(deftype SubFail [pattern])

(defn- sub-value [pattern]
  (constantly [pattern]))

(defn- sub-literal [pattern]
  (constantly [(second pattern)]))

(defn- sub-restartable [pattern]
  (sub* (second pattern)))

(defn- sub-element [pattern]
  (let [name (var-name pattern)]
    (fn [dict fail]
      (if (and fail (= ::none (dict name ::none)))
        (fail dict name pattern)
        (let [v (dict name pattern)]
          (if (instance? SubFail v)
            v
            [(dict name pattern)]))))))

(defn- sub-as [pattern]
  (sub-element (list '? (second pattern))))

(defn- sub-chain [pattern]
  (sub* (second pattern)))

(defn- sub-sequence [pattern]
  (let [name (var-name pattern)]
    (fn [dict fail]
      (if (and fail (= ::none (dict name ::none)))
        (fail dict name pattern)
        (let [r (dict name [pattern])]
          (cond (seqable? r) r
                (instance? SubFail r) r
                :else
                (throw (ex-info (format "Invalid substitution value for sequence pattern %s"
                                        pattern)
                                {:pattern pattern :value r}))))))))

(defn- sub-or-reduced [acc dict fail fail-token]
  (fn [r f]
    (let [s (f dict fail)]
      (if (instance? SubFail s)
        (reduced (if (identical? s fail-token)
                   []
                   s))
        (acc r s)))))

(defn- sub-optional
  ([pattern]
   (sub-optional pattern nil))
  ([pattern parent-fail]
   (let [subs (mapv sub* (rest pattern))
         fail-token (->SubFail pattern)
         my-fail (or parent-fail (constantly fail-token))]
     (fn opt-sub [dict fail]
       (reduce (sub-or-reduced into dict my-fail fail-token)
               [] subs)))))

(defn- sub-if [[_ pred then else :as pattern]]
  (let [fail-token (->SubFail pattern)
        my-fail (constantly fail-token)
        f (resolve-fn pred (constantly nil))
        then (sub-optional ['if then] my-fail)
        else (sub-optional ['if else] my-fail)]
    (fn [dict fail]
      (if f
        (let [r (then dict my-fail)]
          (if (or (= fail-token r)
                  (not (f (first r))))
            (let [r (else dict fail)]
              (if (= fail-token r)
                [pattern]
                r))
            r))
        [pattern]))))

(defn- sub-when [[_ pred & then :as pattern]]
  (let [fail-token (->SubFail pattern)
        my-fail (constantly fail-token)
        f (resolve-fn pred (constantly nil))
        then (sub-optional (list* 'if then) my-fail)]
    (fn [dict fail]
      (if f
        (let [r (then dict my-fail)]
          (if (= fail-token r)
            [pattern]
            (when (f (first r))
              r)))
        [pattern]))))

(defn- sub-map [pattern]
  (let [fail-token (->SubFail pattern)
        my-fail (constantly fail-token)
        s (sub-optional pattern my-fail)]
    (fn [dict fail]
      (let [r (s dict nil)]
        (if (= fail-token r)
          (if fail
            (fail dict nil pattern)
            [pattern])
          (apply hash-map r))))))

(defn- sub-many
  ([pattern]
   (sub-many pattern 0))
  ([pattern at-least]
   (let [fail-token (->SubFail pattern)
         my-fail (constantly fail-token)
         s (sub-optional (cons nil (rest pattern)) my-fail)]
     (fn [dict fail]
       (loop [result []
              depth 0]
         (let [r (s (fn [name _]
                      (let [v (dict name ::none)]
                        (if (= ::none v)
                          fail-token
                          (if (seqable? v)
                            (nth v depth fail-token)
                            v))))
                    nil)]
           (cond (= fail-token r)
                 (if (<= at-least depth)
                   result
                   (if fail
                     (fail dict nil pattern)
                     [pattern]))
                 (instance? SubFail r) r
                 :else (recur (into result r) (inc depth)))))))))

(defn- sub-at-least-one [pattern]
  (sub-many pattern 1))

(defn- sub-list [pattern]
  (let [subs (mapv sub* pattern)
        [mt finalize]
        (cond (instance? clojure.lang.Cons pattern) [() #(into () %)]
              (list? pattern) [() #(into () %)]
              :else [(empty pattern) identity])]
    (fn [dict fail]
      (let [r (reduce (sub-or-reduced into dict fail nil)
                      mt
                      subs)]
        (if (instance? SubFail r)
          r
          [(finalize r)])))))


(defmethod* sub* :value #'sub-value)
(defmethod* sub* '?:literal #'sub-literal)
(defmethod* sub* '?:= #'sub-literal)
(defmethod* sub* '? #'sub-element)
(defmethod* sub* '?? #'sub-sequence)
(defmethod* sub* :list #'sub-list)
(defmethod* sub* '?:? #'sub-optional)
(defmethod* sub* '?:1 #'sub-optional)
(defmethod* sub* '?:* #'sub-many)
(defmethod* sub* '?:+ #'sub-at-least-one)
(defmethod* sub* '?:chain #'sub-chain)
(defmethod* sub* '?:as #'sub-as)
(defmethod* sub* '?:map #'sub-map)
(defmethod* sub* '?:restartable #'sub-restartable)
(defmethod* sub* '?:if #'sub-if)
(defmethod* sub* '?:when #'sub-when)
(defmethod sub* :default [pattern]
  (if (seqable? pattern)
    (sub-list pattern)
    (sub-value pattern)))

(defn substitute
  "Substitute matchers in the given pattern with data in the provided dict.

  If called with just a pattern (arity 1), returns a function that takes data
  and an optional failure continuation (fn [dict name pattern]) which must
  return a *list* of data to be spliced in place of the pattern.

  If using a static pattern, prefer [[matches.r3.rewrite/sub]]."
  ([x]
   (comp first (sub* x)))
  ([x dict]
   ((substitute x) dict nil)))
