(ns compiler-course.pass12-allocate-registers
  (:require
   [compiler-course.dialects :refer :all]
   [compiler-course.r1-allocator :refer [allocate-registers* liveness to-graph
                                         var-locations
                                         with-allocated-registers]]
   [pattern :refer [sub]]))


;; Allocate registers (see r1-allocate ns)

(defn allocate-fn-registers*
  [define]
  (let [g (to-graph (liveness define))
        g (allocate-registers* g)
        [_ d var-types blocks] define
        var-locs (var-locations var-types g)
        blocks (-> (vec (vals blocks))
                   (with-allocated-registers {:loc var-locs}))]
    (sub (define ?d ?var-types ?var-locs ?blocks))))

(defn allocate-registers
  {:=>/from 'Selected :=>/to 'RegAllocated}
  [program]
  (sub (program ~@(map allocate-fn-registers* (rest program)))))
