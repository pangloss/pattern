(ns matches.util
  (:require [clojure.zip :as zip])
  (:import [clojure.lang IMeta IObj]))


(defn meta? [x]
  (or
    (instance? IMeta x)
    (instance? IObj x)))

(defn- build-coll [orig children]
  (with-meta
    (cond (instance? clojure.lang.Cons orig) (list* children)
          (list? orig) (list* children)
          :else (into (empty orig) children))
    (meta orig)))

(defn- make-zipper [x]
  (zip/zipper sequential? seq build-coll x))

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

(defn forward-meta
  "Copy meta over from the elements in the old tree to the new tree until the trees diverge"
  [old-tree new-tree]
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
              (zip/prev rz))))))))

