(ns pattern.substitute
  "This namespace implements a data-driven substitution system. It's flexible
  but much slower than the one defined in the [[pattern.r3.rewrite]] namespace that fully
  precompiles the substitution."
  (:require [pattern.match.core :refer [var-name matcher-type-for-dispatch pattern-names *disable-modes* resolve-fn]]
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

(defn- sub-as [[_ as & [alt] :as pattern]]
  (let [f (sub-element (list '? (second pattern)))
        altf (sub* alt)]
    (fn [dict fail]
      (f dict (fn fail-as [dict' name' pattern']
                (let [r (altf dict
                          (or fail
                            (fn fail-as-alt [dict'' name'' pattern'']
                              [pattern''])))]
                  (if (= r [alt])
                    [pattern]
                    r)))))))

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

(defn- sub-as* [[_ as & [alt] :as pattern]]
  (let [f (sub-sequence (list '?? (second pattern)))
        altf (sub* alt)]
    (fn [dict fail]
      (f dict (fn fail-as [dict' name' pattern']
                (let [r (altf dict
                          (or fail
                            (fn fail-as-alt [dict'' name'' pattern'']
                              [pattern''])))]
                  (if (= r [alt])
                    [pattern]
                    r)))))))

(defn- sub-or [[_ & alts :as pattern]]
  (let [alts (map sub* alts)
        my-fail (->SubFail pattern)]
    (fn [dict fail]
      (let [fail (or fail (constantly my-fail))
            r (reduce
                (fn [r alt]
                  (let [v (alt dict fail)]
                    (if (instance? SubFail v)
                      v
                      (reduced v))))
                [] alts)]
        (if (= r my-fail)
          [pattern]
          r)))))

(defn- sub-and [[_ & alts :as pattern]]
  (let [alts (map sub* alts)
        my-fail (->SubFail pattern)]
    (fn [dict fail]
      (let [fail (or fail (constantly my-fail))
            r (reduce
                (fn [r alt]
                  (let [v (alt dict fail)]
                    (if (instance? SubFail v)
                      (reduced v)
                      v)))
                [] alts)]
        (if (= r my-fail)
          [pattern]
          r)))))

(defn- sub-or-reduced
  "Returns a reducer function with the following behavior.

  If substitution succeeds, the result will be the appended to the resultset.

  Otherwise, if (= fail-token (fail)), the result of the reduce operation will
  be an empty resultset because this will return (reduced []). But if
  (not= fail-token (fail)), the result will be (reduced (fail)), ie. some other fail
  token. "
  [acc dict fail fail-token]
  (fn [r subf]
    (let [s (subf dict fail)]
      (if (instance? SubFail s)
        (reduced (if (identical? s fail-token)
                   []
                   s))
        (acc r s)))))

(defn- sub-optional
  "Will try to make substitutions for the pattern, but if substitution fails,
  returns an empty resultset.

  The behavior can be modified if given a parent-fail function, in which case
  the fail token will be returned to be handled at the parent level. "
  ([pattern]
   (sub-optional pattern nil))
  ([pattern parent-fail]
   (let [subs (mapv sub* (rest pattern))
         fail-token (->SubFail pattern)
         my-fail (or parent-fail (constantly fail-token))]
     (fn opt-sub [dict fail]
       (let [r (reduce (sub-or-reduced into dict my-fail fail-token)
                 [] subs)]
         (if (and (not parent-fail) (every? nil? r))
           []
           r))))))

(defn- sub-one [pattern]
  (let [subs (mapv sub* (rest pattern))
        fail-token (->SubFail pattern)
        my-fail (fn [dict name pattern] [pattern])]
    (fn opt-sub [dict fail]
      (let [r (reduce
                (sub-or-reduced into dict my-fail fail-token)
                [] subs)]
        (if (= r (rest pattern)) [pattern] r)))))

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
    (if (odd? (count (rest pattern)))
      (throw (ex-info "Invalid map pattern. Must have an even number of pattern elements"
               {:pattern pattern}))
      (fn [dict fail]
        (let [r (s dict nil)]
          (if (= fail-token r)
            (if fail
              (fail dict nil pattern)
              [pattern])
            [(apply hash-map r)]))))))

(defn- sub-many-map [[_ k* v* :as pattern]]
  (let [kf (sub* k*)
        vf (sub* v*)]
    (if (not= 3 (count pattern))
      (throw (ex-info "Invalid zipmap pattern. Must have exactly 2 pattern elements"
               {:pattern pattern}))
      (fn [dict fail]
        (let [k (kf dict fail)
              v (vf dict fail)]
          (cond (instance? SubFail k) k
                (instance? SubFail v) v
                (and (sequential? (first k)) (sequential? (first v)))
                [(zipmap (first k) (first v))]
                fail (fail dict nil pattern)
                :else [pattern]))))))

(defn- sub-set [[_ item* :as pattern]]
  (let [itemf (sub* item*)]
    (if (not= 2 (count pattern))
      (throw (ex-info "Invalid pattern. Must have exactly 1 pattern element"
               {:pattern pattern}))
      (fn [dict fail]
        (let [item (itemf dict fail)]
          (cond (instance? SubFail item) item
                (sequential? (first item))
                [(set (first item))]
                fail (fail dict nil pattern)
                :else [pattern]))))))

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

(defn- sub-at-least-one-map [pattern])

(defmethod* sub* :value #'sub-value)
(defmethod* sub* '?:literal #'sub-literal)
(defmethod* sub* '?:= #'sub-literal)
(defmethod* sub* '? #'sub-element)
(defmethod* sub* '?? #'sub-sequence)
(defmethod* sub* :list #'sub-list)
(defmethod* sub* '?:? #'sub-optional)
(defmethod* sub* '?:1 #'sub-one)
(defmethod* sub* '?:* #'sub-many)
(defmethod* sub* '?:+ #'sub-at-least-one)
(doseq [alias '[?:*map ?:+map ?:map* ?:map+]]
  (defmethod* sub* alias #'sub-many-map))
(defmethod* sub* '?:chain #'sub-chain)
(defmethod* sub* '?:as #'sub-as)
(defmethod* sub* '?:as* #'sub-as*)
(defmethod* sub* '?:map #'sub-map)
(defmethod* sub* '?:set #'sub-set)
(defmethod* sub* '?:restartable #'sub-restartable)
(defmethod* sub* '?:if #'sub-if)
(defmethod* sub* '?:when #'sub-when)
(defmethod* sub* '| #'sub-or)
(defmethod* sub* '& #'sub-and)
(defmethod sub* :default [pattern]
  (if (seqable? pattern)
    (sub-list pattern)
    (sub-value pattern)))

(defn substitute
  "Substitute matchers in the given pattern with data in the provided dict.

  If called with just a pattern (arity 1), returns a function that takes data
  and an optional failure continuation (fn [dict name pattern]) which must
  return a *list* of data to be spliced in place of the pattern.

  If using a static pattern, prefer [[pattern.r3.rewrite/sub]]."
  ([x]
   (comp first (sub* x)))
  ([x dict]
   ((substitute x) dict nil)))
