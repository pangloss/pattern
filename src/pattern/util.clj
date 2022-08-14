(ns pattern.util
  (:require [clojure.zip :as zip]
            [diffit.vec :as d]
            [clojure.set :as set])
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

(defn skip
  "Moves to the next sibling or next point in the hierarchy, depth-first. When
  reaching the end, returns a distinguished loc detectable via end?. If already
  at the end, stays there."
  [loc]
  (if (zip/end? loc)
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

(defn walk-equal-subtree
  "A special op-type may be used for the first element, after that it's always :="
  [oz rz on-same op-type]
  (let [stop (zpos (skip oz))]
    (loop [oz oz
           rz rz
           op-type op-type]
      (if (= (zpos oz) stop)
        rz
        (let [on (zip/node oz)
              rz (if on-same
                   (on-same op-type rz on)
                   rz)]
          (if (= on (zip/node rz)) ;; unchanged by callback
            ;; If a data structure is changed, that messes up the zipper because
            ;; it walks into the newly added thing. If we detect that, we skip
            ;; any further walk into that element.
            (recur (zip/next oz)
              (zip/next rz)
              :=)
            (recur (skip oz) (skip rz) :=)))))))

(defn simple-diff
  "Return the indices with added and removed elements"
  [old nw]
  (let [om? (map? old)
        nm? (map? nw)]
    (if (not= om? nm?)
      []
      (let [old (vec (if om? (map->sorted old) old))
            nw (vec (if nm? (map->sorted nw) nw))]
        (loop [r (transient [])
               pos 0
               opos 0
               [[side idx els] :as d] (second (d/diff old nw))]
          (if side
            (if (= pos idx)
              (if (= :+ side)
                (if-let [els (next els)]
                  (recur (conj! r [:+ pos opos (nw pos)]) (inc pos) opos (cons [side (inc idx) els] (rest d)))
                  (recur (conj! r [:+ pos opos (nw pos)]) (inc pos) opos (rest d)))
                (if (< 1 els)
                  (recur (conj! r [:- pos opos (old opos)]) pos (inc opos) (cons [side idx (dec els)] (rest d)))
                  (recur (conj! r [:- pos opos (old opos)]) pos (inc opos) (rest d))))
              (recur r idx (+ opos (- idx pos)) d))
            (persistent! r)))))))

(defn distinct-by-2
  "Returns a vector of the elements of coll with duplicates of the result
  of calling get-a or get-b removed."
  {:static true}
  ([get-a get-b coll]
   (loop [result (transient [])
          [f :as xs] coll
          seen-a #{}
          seen-b #{}]
     (if xs
       (let [a (get-a f)
             b (get-b f)]
         (if (or (contains? seen-a a) (contains? seen-b b))
           (recur result (next xs) seen-a seen-b)
           (recur (conj! result f) (next xs) (conj seen-a a) (conj seen-b b))))
       (persistent! result)))))

(defn- similarity
  "Heuristics upon heuristics. More negative is better.

  Different type = not similar
  position = 8 - (2 * distance)
  length = 2 * common length - 2 * length difference
  prefix = 5 * number of identical prefix items"
  [[a ai] [r ri]]
  ;; This can probably be tuned better.
  ;; It does not include edit distance or set intersection metrics in the heuristic
  (if (or (and
            (or (sequential? a) (map? a))
            (= (type a) (type r)))
        (and (listy? a) (listy? r)))
    (let [score (+ (- 8 (* (abs (- ai ri)) 3))
                  (let [ca (count a)
                        cr (count r)]
                    (- (* (min ca cr) 2) (* (abs (- ca cr)) 2))))]
      (- ;; negate the result for better sorting.
        (if (map? a)
          ;; map uses key intersection count:
          (* 6 (count (set/intersection (set (keys a)) (set (keys r)))))
          ;; lists use prefix equality:
          (loop [score score a a r r]
            (if (and a r (= (first a) (first r)))
              (recur (+ score 6) (next a) (next r))
              score)))))
    ;; Current plan is to filter out matches if score <= 0. Sometimes things are
    ;; added and other things are removed and they are not related.
    0))

(defn- best-pairs
  "Find the best matching pairs according to the [[similarity]] heuristic.

  Adds and removes must be like this:

      (let [adds [[added-form idx-in-new] ...]
            removes [[removed-form idx-in-old] ...]] ...)

  Returns a map of:

      {idx-in-new [idx-in-old similarity removed-form]}"
  [adds removes]
  (let [r (->>
            (for [a adds
                  r removes
                  :let [s (similarity a r)]
                  :when (neg? s)]
              [a r s])
            (sort-by #(nth % 2))
            (distinct-by-2 #(nth % 0) #(nth % 1)))]
    (reduce (fn [m [a r s]]
              (assoc m (nth a 1) [(nth r 1) s (nth r 0)]))
      {}
      r)))

(defn map-changes [d]
  (let [changes (into {} (comp
                           (filter #(= 2 (count (val %))))
                           (map (fn [[_ [a b]]]
                                  (let [[[_ pos :as edit] [_ opos _ form]] (if (= :+ (first a)) [a b] [b a])]
                                    [edit [pos [opos -1 form]]]))))
                  (group-by (comp key last) d))]
    (into {}
      (keep #(changes %))
      d)))

(defn find-changes
  "Given a [[simple-diff]] result, return a map of moves and a map of changes.

  See [[diff]] for the final diff output incorporating changes."
  [d]
  (let [groups (group-by last d)]
    (loop [moves {}
           new []
           old []
           [[form group] & groups] groups]
      (if group
        (let [diffs (group-by first group)]
          (if (= 1 (count diffs))
            (recur moves
              (into new (:+ diffs))
              (into old (:- diffs))
              groups)
            (let [adds (:+ diffs)
                  removes (:- diffs)
                  c (min (count adds) (count removes))]
              (recur
                (into moves (map (fn [add remove]
                                   [(nth add 1) [(nth remove 2) 0 (last remove)]])
                              adds removes))
                (into new (drop c adds))
                (into old (drop c removes))
                groups))))
        [moves (best-pairs
                 (keep (fn [[_ i _ f]] (when (sequential? f) [f i])) new)
                 (keep (fn [[_ _ i f]] (when (sequential? f) [f i])) old))]))))

(defn diff
  "Returns a diff that includes :+ and :- for adds and removes but also :m and :c for moves and changes.

  Each entry is:
      [op-type result-pos orig-pos new-or-orig-form]"
  [old new]
  (let [d (simple-diff old new)
        [moves changes] (if (map? old)
                          [{} (map-changes d)]
                          (find-changes d))
        changes (merge moves changes)
        ;; remove indices that are part of moves or changes so not needed in the diff
        by-opos (group-by (comp first val) changes)]
    (loop [result (transient [])
           pos 0
           opos 0
           [[side idx :as edit] & d] d]
      (if side
        (if (= pos idx)
          (case side
            :+ (if-let [[oidx sim orig] (changes pos)]
                 (recur (conj! result [(if (= 0 sim) :m :c) pos oidx orig]) (inc pos) opos d)
                 (recur (conj! result edit) (inc pos) opos d))
            :- (if-let [removals (by-opos opos)]
                 (recur result pos (inc opos) d)
                 (recur (conj! result edit) pos (inc opos) d)))
          (recur result idx (+ opos (- idx pos)) (cons edit d)))
        (persistent! result)))))

;; TODO: add ability to skip a branch if it has a metadata marker. That can be used
;; to mark that metadata has already been merged, or that metadata should not be merged.
;;

(defn walk-diff*
  "See [[walk-diff]]. This version takes a diff and a zipper which has been
  traversed to the index 0 position relative to the diff."
  [d oz rz on-same on-changed]
  (if-let [rz (zip/down rz)]
    (let [oz (or (zip/down oz) [nil :end])
          op (zip/path oz)
          rp (zip/path rz)]
      (loop [c 0
             d d
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
          (let [[side idx _ orig] (first d)]
            (if (or (nil? idx) (< c idx))
              (recur (inc c) d (skip oz) (walk-equal-subtree oz rz on-same :=))
              (case side
                :m (let [movez (make-zipper+map orig)]
                     (recur (inc c) (rest d) (skip oz) (walk-equal-subtree movez rz on-same :m)))

                :c (let [changez (make-zipper+map orig)]
                     (recur (inc c) (rest d) (skip oz)
                       (let [rz (if on-changed (on-changed side rz (zip/node changez)) rz)]
                         ;; changes should always be data structures
                         (walk-diff*
                           (diff (zip/node changez) (zip/node rz))
                           changez rz on-same on-changed))))

                :+ (recur (inc c) (rest d) oz (skip (if on-changed (on-changed side rz nil) rz)))
                :- (recur c (rest d)
                     (skip oz) (if on-changed (on-changed side rz (zip/node oz)) rz))))))))
    (skip rz)))

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
  (when (some? new)
    (let [old (if (some? old)
                old
                (if (collection? new)
                  (empty new)
                  old))]
      (zip/root
        (walk-diff* (diff old new)
          (make-zipper+map old)
          (make-zipper+map new)
          on-same on-changed)))))

(defn deep-merge-meta
  "Copy metadata over from the elements in the old tree to the new tree as
  comprehensively as possible."
  ([old-tree new-tree]
   (deep-merge-meta old-tree new-tree merge))
  ([old-tree new-tree combine-meta]
   (if (and (collection? old-tree) (collection? new-tree))
     (let [oz (make-zipper+map old-tree)
           rz (make-zipper+map new-tree)
           d (diff old-tree new-tree)]
       (letfn [(on-same [op rz on]
                 (if (meta? on)
                   (zip/edit rz #(with-meta % (combine-meta (meta on) (meta %))))
                   rz))
               (on-changed [op rz orig]
                 (if (and (= :c op) (meta? orig))
                   (zip/edit rz #(with-meta % (combine-meta (meta orig) (meta %))))
                   rz))]
         (if (seq d)
           (zip/root (walk-diff* d oz rz on-same on-changed))
           (zip/root (walk-equal-subtree oz rz on-same :=))))))))

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
