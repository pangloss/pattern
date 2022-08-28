(ns pattern.util
  (:require [clojure.zip :as zip]
            [diffit.vec :as d]
            [clojure.set :as set]
            [clojure.walk :as walk])
  (:import [clojure.lang IMeta IObj]))

(defn listy?
  "Returns true if x is any kind of list except a vector."
  [x]
  (and (sequential? x) (not (vector? x))))

(defn ints?
  "Return true if x is an int array

  The Java byte-array / bytes? type is signed. That makes a mess, so we use ints."
  [x] (if (nil? x)
        false
        (instance? clojure.lang.ArraySeq$ArraySeq_int (seq x))))

(defn arrayseq?
  "Returns true if the object is any sort of non-empty Java Array.

  Will return false if the array is empty.

  This may still need to be extened to be complete."
  [x]
  (if (nil? x)
    false
    (instance? clojure.lang.ArraySeq (seq x))))


(defn meta?
  "Returns true if the object supports attaching metadata via with-meta."
  [x]
  (or
    (instance? IMeta x)
    (instance? IObj x)))

(defn meta=
  "Returns true if the metadata attached to a is equal to the metadata attached to b."
  [a b]
  (= (meta a) (meta b)))

(defn all-equiv?
  "For use as the equiv? argument in rule combinators.

  Data, metadata on the data, and env must all be equal.

  In :no-env mode, ignore env difference.

  See also [[equiv?]]"
  ([mode]
   (case mode
     :no-env
     (fn [datum orig-env done env]
       (and (= done datum) (meta= done datum)))
     all-equiv?))
  ([datum orig-env done env]
   (and (= done datum) (meta= done datum) (= orig-env env))))

(defn meta-equiv?
  "For use as the equiv? argument in rule combinators.

  metadata and env must be equal.

  In :no-env mode, ignore env difference.

  See also [[equiv?]]"
  ([mode]
   (case mode
     :no-env
     (fn [datum orig-env done env]
       (meta= done datum))
     all-equiv?))
  ([datum orig-env done env]
   (and (meta= done datum) (= orig-env env))))

(defn equiv?
  "For use as the equiv? argument in rule combinators.

  Data and env should be equal, but ignore metadata.

  In :no-env mode, just look at data, ignore both env and metadata.

  See also [[all-equiv?]]"
  ([mode]
   (case mode
     :no-env
     (fn [datum orig-env done env]
       (= done datum))
     equiv?))
  ([datum orig-env done env]
   (and (= done datum) (= orig-env env))))

(defn build-coll [orig children]
  (let [coll (cond (instance? clojure.lang.Cons orig) (list* children)
                   (chunked-seq? orig) (list* orig)
                   (instance? clojure.lang.LazySeq orig) (list* orig)
                   (list? orig) (list* children)
                   (map-entry? orig) (vec children)
                   (map? orig) (into {} children)
                   (vector? orig) (into [] children)
                   (ints? orig) (int-array children)
                   (arrayseq? orig) children
                   :else (throw (ex-info "unknown coll" {:type (type orig) :orig orig})))]
    (if (meta? coll)
      (with-meta coll (meta orig))
      coll)))

(defn make-zipper
  "Make a zipper that will descend into any type of sequential objects except maps."
  [x]
  (if (nil? x)
    [nil :end]
    (zip/zipper sequential? seq build-coll x)))

(defn collection?
  "Is x a sequential collection, a map or a map-entry?"
  [x]
  (or (sequential? x) (map? x) (map-entry? x)))

(defn map->sorted [x]
  (try (sort-by key x)
       (catch Exception e
         (sort-by (comp hash key) x))))

(defn make-zipper+map
  "Make a zipper that will descend into any type of sequential objects,
  including maps."
  [x]
  (if (nil? x)
    [nil :end]
    (zip/zipper collection?
      (fn [x]
        (if (map? x)
          (map->sorted x)
          (seq x)))
      build-coll x)))

(defn walk-with-paths
  "Like [[clojure.walk/walk]] got combined with [[map-indexed]]. Calls
  [[(inner idx element)]] and [[(outer idx element)]] where idx is a vector that
  can be used with functions like [[get-in]] or [[update-in]]

  Map keys are given the path to the map with :map/key appended. For instance, when
  the traversing the below map gets to the :k element, the callbacks would be called
  as shown:

    [_ {:x [{:k :v}]}]

    (inner [1 :x 0 :key] :k)"
  [inner outer path form]
  (let [inner* (fn [i x] (inner (conj path i) x))]
    (cond
      (list? form) (outer path (with-meta (apply list (map-indexed inner* form))
                                  (meta form)))
      (instance? clojure.lang.IMapEntry form)
      (outer path (clojure.lang.MapEntry/create
                     (inner (conj (subvec path 0 (dec (count path))) (key form) :map/key) (key form))
                     (inner (conj (subvec path 0 (dec (count path))) (key form)) (val form))))
      (seq? form) (outer path (with-meta (doall (map-indexed inner* form))
                                (meta form)))
      (instance? clojure.lang.IRecord form)
      ;; I assume records maintain or update their metadata correctly:
      (outer path (first (reduce
                           (fn [[r i] x]
                             [(conj r (inner (conj path i) x)) (inc i)])
                           [form 0]
                           form)))
      (coll? form) (outer path (with-meta
                                 (into (empty form) (map-indexed inner* form))
                                 (meta form)))
      :else (outer path form))))

(defn postwalk-with-paths
  "Performs a depth-first, post-order traversal of form.  Calls (f idx subform)
  on each sub-form, uses f's return value in place of the original.
  Recognizes all Clojure data structures. Consumes seqs as with doall.

  See [[clojure.walk/postwalk]] and [[walk-with-paths]]."
  ([f form]
   (postwalk-with-paths f [] form))
  ([f path form]
   (walk-with-paths (partial postwalk-with-paths f) f path form)))


(defn find-in
  "Like get-in, but works with non-indexed collections, too.

  Also handles :map/key in path that returns the actual key element from the
  collection. The actual key may have different metadata than the value used to
  look it up."
  [[idx & path] form]
  (let [item
        (if (associative? form)
          (if (= :map/key (first path))
            (key (find form idx))
            (if (map? form)
              (get form idx)
              (when (int? idx)
                (get form idx nil))))
          (when (int? idx)
            (nth form idx)))]
    (if (and (seq path) (not= [:map/key] path))
      (if (= :map/key (first path))
        (recur (rest path) item)
        (recur path item))
      item)))

(defn postwalk-with-meta
  "Like [[postwalk]] but copies source metadata to the result."
  [f form]
  (walk/walk
    (fn [element]
      (let [result (postwalk-with-meta f element)]
        (if-let [md (meta element)]
          (if (meta? result)
            (vary-meta result #(merge md %))
            result)
          result)))
    f
    form))

(defn postwalk-replace-with-meta
  "Like [[postwalk-replace]] but preserves metadata"
  [smap form]
  (postwalk-with-meta (fn [x] (if (contains? smap x) (smap x) x)) form))
