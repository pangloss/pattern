(ns pattern.util
  (:require [clojure.zip :as zip]
            [diffit.vec :as d]
            [clojure.zip :as z])
  (:import [clojure.lang IMeta IObj]))

(defn ints?
  "Return true if x is an int array

  The Java byte-array / bytes? type is signed. That makes a mess, so we use ints."
  [x] (if (nil? x)
        false
        (instance? clojure.lang.ArraySeq$ArraySeq_int (seq x))))

(defn array? [x]
  (if (nil? x)
    false
    (instance? clojure.lang.ArraySeq (seq x))))


(defn meta? [x]
  (or
    (instance? IMeta x)
    (instance? IObj x)))

(defn build-coll [orig children]
  (let [coll (cond (instance? clojure.lang.Cons orig) (list* children)
                   (chunked-seq? orig) (list* orig)
                   (instance? clojure.lang.LazySeq orig) (list* orig)
                   (list? orig) (list* children)
                   (map-entry? orig) (vec children)
                   (map? orig) (into {} children)
                   (vector? orig) (into [] children)
                   (ints? orig) (int-array children)
                   (array? orig) children
                   :else (throw (ex-info "unknown coll" {:type (type orig) :orig orig})))]
    (if (meta? coll)
      (with-meta coll (meta orig))
      coll)))

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

(defn zpos [z]
  (z 1))

(defn walk-equal-subtree [oz rz f]
  (let [stop (zpos (skip oz))]
    (loop [oz oz
           rz rz]
      (if (= (zpos oz) stop)
        rz
        (let [on (zip/node oz)]
          (recur (zip/next oz)
            ;; note this is identical
            (zip/next (zip/edit rz f on #_#_with-meta (merge (meta on) (meta rn))))))))))

;; example for walk-diff: ! means nodes are equal, . is no change, + is skip forward, L is old, R is new
;; ! ! 0 [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c < i, equal nodes
;; . + 1 [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c = i, :+ advance R
;; ! ! 2 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c < i, equal nodes
;; . + 3 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c = i, :+ advance R
;; . + 4 [           [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]] c <= i + (len a), :+ advance R
;; + . 5 [                                                                         [:- 5 1]] c = i, :- advance L
;; ! ! 6 [] no diffs, all further nodes equal
(defn simple-diff [a b]
  (mapv (fn [[side idx els]]
          (if (vector? els)
            [side idx (dec (count els))]
            [side idx (dec els)]))
    (second (d/diff a b))))

(defn diff [a b]
  (let [d (simple-diff a b)]
    (first
      (reduce
        (fn [[r a] b]
          (if (and (not= (a 0) (b 0)) ;; add/remove
                ;; ops are adjacent
                (= (inc (+ (a 1) (a 2))) (b 1))
                ;; same length
                (= (a 2) (b 2)))
            ;; it's a replacement
            [(assoc r (dec (count r)) [:r (a 1) (a 2)])
             b]
            ;; regular change
            [(conj r b) b]))
        [[(first d)] (first d)]
        (rest d)))))


(defn walk-diff [d oz rz same changed]
  (let [op (zip/path oz)
        rp (zip/path rz)]
    (loop [c 0
           [[side idx ec] :as d] d
           oz oz
           rz rz]
      (if (or (zip/end? oz) (zip/end? rz)
            ;; don't leave the current nesting level
            (not= op (zip/path oz))
            (not= rp (zip/path rz)))
        rz
        (if (< c idx)
          (recur (inc c) d (skip oz) (walk-equal-subtree oz rz same))
          (let [d (if (= c (+ idx ec))
                    (rest d)
                    d)]
            (case side
              :r (recur (inc c) d (skip oz)
                   (if (and (zip/branch? oz) (zip/branch? rz))
                     (walk-diff (diff (zip/node oz) (zip/node rz)) (zip/down oz) (zip/down rz) same changed)
                     (skip rz)))
              :+ (recur (inc c) d oz (skip rz))
              :- (recur (inc c) d (skip oz) rz)))))
      #_
      (if (zero? idx)
        (let [on (zip/node oz)
              nn (zip/node nz)]
          (if (= on nn)
            ;; identical node or subtree
            (if (zip/branch? oz)
              (recur (skip oz) (skip nz) (walk-equal-subtree oz rz same))
              (recur (zip/next oz) (zip/next nz)
                ;; note this is identical
                (zip/next (zip/edit rz with-meta (merge (meta on) (meta nn))))))
            (if (and (zip/branch? oz) (zip/branch? nz))
              ())
            (if (= (type on) (type nn)))))))))

(defn deep-merge-meta2
  "Copy meta over from the elements in the old tree to the new tree until the trees diverge"
  ([old-tree new-tree]
   (deep-merge-meta2 old-tree new-tree merge))
  ([old-tree new-tree f]
   (if (and (sequential? old-tree) (sequential? new-tree))
     (let [oz (make-zipper old-tree)
           nz (make-zipper new-tree)
           rz nz
           d (second (diff old-tree new-tree))]
       (if (seq d)
         (zip/root (walk-diff d oz rz same nil))
         (zip/root (walk-equal-subtree oz rz same)))))))



(comment
  (diff [:a :b  1 2 3] [:x :y 1 2 3 4])
  ;; => [[:r 1 0] [:+ 1 0] [:+ 1 0]]


  (let [z (make-zipper [[1 2] 3 4])]
    (-> z zip/next
      zip/next
      zip/path))


  (simple-diff
    '(program 0 1 2 3)
    '(program 0  9  3))

  (let [a '(program 0 9 2 3)
        b '(program 0 9 9 3)]
    (walk-diff (diff a b) (zip/down (make-zipper a)) (zip/down (make-zipper b))
      (fn [b a] (prn :same :from a :to b) b)))

  [[:+ 1 [0]]
   [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]]
   [:- 5 1]]
  ;; => [[:+ 1 [0]] [:+ 3 [42 8]] [:- 5 1]]
  ;; => [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2)))]] [:- 4 1]]
  ;; => [[:+ 1 [0]] [:+ 3 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))) 8]] [:- 5 1]]

                                        ;diffit
  [2 [[:- 1 1]
      [:+ 1 [(let [a 1] (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2)))]]]]
  ;; => [2 [[:- 1 1] [:+ 1 [42]]]]

  ;; astar
  [[[1 1 2] :-]
   [[1 1 2] :-]
   [[1 2] :r (let [b 2] (+ (+ (+ (+ a 36) b) 1) 2))]]


  ;; quick:
  '[[[1 1 2] :-]
    [[1 1 2] :-]
    [[1 2 0] :-]
    [[1 2 0] :-]
    [[1 2 0] :-]
    [[1 2 0] :r let]
    [[1 2 1] :r [b 2]]
    [[1 2 2] :r (+ (+ (+ (+ a 36) b) 1) 2)]])
