(ns pattern.util
  (:require [clojure.zip :as zip])
  (:import [clojure.lang IMeta IObj]))


(defn meta? [x]
  (or
    (instance? IMeta x)
    (instance? IObj x)))

(defn build-coll [orig children]
  (with-meta
    (cond (instance? clojure.lang.Cons orig) (list* children)
          (chunked-seq? orig) (list* orig)
          (instance? clojure.lang.LazySeq orig) (list* orig)
          (list? orig) (list* children)
          (map-entry? orig) (vec children)
          (map? orig) (into {} children)
          (vector? orig) (into [] children)
          :else (throw (ex-info "unknown coll" {:type (type orig) :orig orig})))
    (meta orig)))

(defn make-zipper [x]
  (zip/zipper sequential? seq build-coll x))

(defn make-zipper+map [x]
  (zip/zipper (some-fn sequential? map? map-entry?) seq build-coll x))

(defn- find-last-equiv-node [ot nt]
  (loop [oz (make-zipper ot)
         nz (make-zipper nt)
         rz (make-zipper nt)]
    (let [on (zip/node oz)
          nn (zip/node nz)]
      (if (or
            (= on nn)
            (and (zip/branch? oz)
              (zip/branch? nz)
              (= (empty on) (empty nn))))
        (if (or (zip/end? (zip/next oz))
              (zip/end? (zip/next nz)))
          [oz nz rz]
          (recur (zip/next oz) (zip/next nz) (zip/next rz)))
        [(zip/prev oz) (zip/prev nz) (zip/prev rz)]))))

(defn deep-merge-meta
  "Copy meta over from the elements in the old tree to the new tree until the trees diverge"
  ([old-tree new-tree]
   (deep-merge-meta old-tree new-tree merge))
  ([old-tree new-tree merge]
   (if (and (sequential? old-tree) (sequential? new-tree))
     (let [[oz nz rz] (find-last-equiv-node old-tree new-tree)]
       (loop [oz oz
              nz nz
              rz rz]
         (let [on (zip/node oz)
               nn (zip/node nz)]
           (if (not (zip/prev nz))
             (if (and (meta on) (meta? nn))
               (with-meta (zip/node rz) (merge (meta on) (meta nn)))
               nn)
             (recur
               (zip/prev oz)
               (zip/prev nz)
               (if (and (meta on) (meta? nn))
                 (zip/prev (zip/edit rz with-meta (merge (meta on) (meta nn))))
                 (zip/prev rz)))))))
     new-tree)))
