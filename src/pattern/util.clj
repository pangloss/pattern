(ns pattern.util
  (:require [clojure.zip :as zip]
            [diffit.vec :as d])
  (:import [clojure.lang IMeta IObj]))

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
  (zip/zipper sequential? seq build-coll x))

(defn collection?
  "Is x a sequential collection, a map or a map-entry?"
  [x]
  (or (sequential? x) (map? x) (map-entry? x)))

(defn make-zipper+map
  "Make a zipper that will descend into any type of sequential objects,
  including maps."
  [x]
  (zip/zipper collection?
    (fn [x]
      (if (map? x)
        (try (sort-by key x)
             (catch Exception e
               (sort-by (comp hash key) x)))
        (seq x)))
    build-coll x))

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

(defn skip
  "Moves to the next sibling or next point in the hierarchy, depth-first. When
  reaching the end, returns a distinguished loc detectable via end?. If already
  at the end, stays there."
  [loc]
  (if (= :end (loc 1))
    loc
    (or
      (zip/right loc)
      (loop [p loc]
        (if (zip/up p)
          (or (zip/right (zip/up p)) (recur (zip/up p)))
          [(zip/node p) :end])))))

(defn- zpos
  "Return the raw position construct in the zipper."
  [z]
  (nth z 1))

(defn walk-equal-subtree [oz rz on-same]
  (let [stop (zpos (skip oz))]
    (loop [oz oz
           rz rz]
      (if (= (zpos oz) stop)
        rz
        (let [on (zip/node oz)]
          (recur (zip/next oz)
            (zip/next (if on-same
                        (on-same rz on)
                        rz))))))))

;; example for walk-diff: ! means nodes are equal, . is no change, + is skip forward, L is old, R is new
;; ! ! 0 [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c < i, equal nodes
;; . + 1 [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c = i, :+ advance R
;; ! ! 2 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c < i, equal nodes
;; . + 3 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c = i, :+ advance R
;; . + 4 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c <= i + (len a), :+ advance R
;; + . 5 [                                                                         [:- 5 1]] c = i, :- advance L
;; ! ! 6 [] no diffs, all further nodes equal
(defn- simple-diff
  "See [[diff]]."
  [a b]
  (mapv (fn [[side idx els]]
          (if (vector? els)
            [side idx (count els)]
            [side idx els]))
    (second (d/diff a b))))

(defn diff
  "Starts with diffit.vec/diff, simplifies the representation and detects replacements.

  Each entry is a tuple of [side idx length]. Side can be :+ :- or -r.

  idx is the position with previous diff entries applied. A :- entry does not
  increment the current index, but others do."
  [a b]
  (let [d (simple-diff a b)]
    (first
      (reduce
        (fn [[r [sa ia ca]] [sb ib cb :as b]]
          (if (or (and (= :+ sa) (= :- sb) ;; add/remove
                    ;; ops are adjacent and same length
                    (= (+ ia ca) ib) (= ca cb))
                (and
                  (= :- sa) (= :+ sb) ;; remove/add
                  ;; same index and length
                  (= ia ib) (= ca cb)))
            ;; it's a replacement
            [(assoc r (dec (count r)) [:r ia ca])
             [:placeholder -1 -1]]
            ;; regular change
            [(conj r b) b]))
        [[(first d)] (first d)]
        (rest d)))))

;; TODO: better handling of changes and insertions/deletions in series. Now it
;; treats them as adds/removes, but I should try to detect changed structures.
;; Maybe a diff metric on the first level in? Maybe try to match up changes? Can
;; I deal with reordering?
;; TODO: add ability to skip a branch if it has a metadata marker. That can be used
;; to mark that metadata has already been merged, or that metadata should not be merged.

(defn walk-diff*
  "See [[walk-diff]]. This version takes a diff and a zipper which has been
  traversed to the index 0 position relative to the diff."
  [d oz rz on-same on-changed]
  (let [op (zip/path oz)
        rp (zip/path rz)]
    (loop [c 0
           [[side idx ec] :as d] d
           oz oz
           rz rz]
      (cond
        (or (zip/end? rz)
          ;; don't leave the current nesting level
          (not= rp (zip/path rz)))
        rz

        (or (zip/end? oz)
          ;; don't leave the current nesting level
          (not= op (zip/path oz)))
        ;; there is added stuff in rz not in oz
        (recur (inc c) d oz (skip (if on-changed (on-changed :+ rz nil) rz)))

        :else
        (if (or (nil? idx) (< c idx))
          (recur (inc c) d (skip oz) (walk-equal-subtree oz rz on-same))
          (let [d (if (= (inc c) (+ idx ec))
                    (rest d)
                    d)]
            (case side
              :r (recur (inc c) d (skip oz)
                  (let [rz (if on-changed (on-changed side rz (zip/node oz)) rz)]
                    (if (and (zip/branch? oz) (zip/branch? rz))
                      (walk-diff*
                        (diff (zip/node oz) (zip/node rz))
                        (zip/down oz) (zip/down rz) on-same on-changed)
                      (skip rz))))
              :+ (recur (inc c) d oz (skip (if on-changed (on-changed side rz nil) rz)))
              :- (recur c (if (= 1 ec)
                            d
                            (cons [side idx (dec ec)] (rest d)))
                   (skip oz) (if on-changed (on-changed side rz (zip/node oz)) rz)))))))))

(defn walk-diff
  "Walks zippers over the old and new data structures in tandem, accounting for
  changes detected via [[diff]]. Calls a callback for either on-same or on-changed.

  The callbacks must return the zipper which they may edit, but if they edit
  they must ensure that the returned zipper is in the correct place so that when
  [[skip]] is called it moves to the correct next element.

  Note that values considered to be the same may not have the same metadata. This
  tool was written to facilitate transferring metadata from one structure to another.

  Callback signatures are:

      (on-same result-zipper orig-value)
      (on-changed change-type result-zipper orig-value-or-nil)"
  [old new on-same on-changed]
  (zip/root
    (walk-diff* (diff old new)
      (zip/down (make-zipper+map old))
      (zip/down (make-zipper+map new))
      on-same on-changed)))

(defn deep-merge-meta2
  "Copy metadata over from the elements in the old tree to the new tree as
  comprehensively as possible."
  ([old-tree new-tree]
   (deep-merge-meta2 old-tree new-tree merge))
  ([old-tree new-tree combine-meta]
   (if (and (collection? old-tree) (collection? new-tree))
     (let [oz (make-zipper+map old-tree)
           rz (make-zipper+map new-tree)
           d (diff old-tree new-tree)]
       (letfn [(on-same [rz on]
                 (if (meta? on)
                   (zip/edit rz #(with-meta % (combine-meta (meta on) (meta %))))
                   rz))
               (on-changed [op rz orig]
                 (tap> [(type orig) (type (zip/node rz))])
                 (if (and (= :r op) (meta? orig) (collection? orig) (= (type orig) (type (zip/node rz))))
                   (zip/edit rz #(with-meta % (combine-meta (meta orig) (meta %))))
                   rz))]
         (if (seq d)
           (zip/root (walk-diff* d (zip/down oz) (zip/down rz) on-same on-changed))
           (zip/root (walk-equal-subtree oz rz on-same))))))))

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
  {:added "1.1"}
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
