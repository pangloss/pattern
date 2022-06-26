(ns compiler-course.pass12-allocate-registers
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  caller-saved-registers callee-saved-registers
                                                  var-locations with-allocated-registers]]
            [compiler-course.dialects :refer [r1-keyword?]]
            [matches.nanopass.dialect :refer [all-dialects =>:to show-parse]]
            [matches :refer [descend in gennice niceid directed on-subexpressions rule rule-list rule-list!
                             descend-all sub success subm rule-simplifier matcher
                             => dialects validate ok ok?]]
            [matches.types :refer [child-rules]]
            [clojure.string :as str]))


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
