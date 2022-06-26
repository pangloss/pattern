(ns compiler-course.pass10-uncover-locals
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


;; Uncover locals

(def uncover-locals
  (dialects
   (=> Explicit Uncovered)
   (directed
    (rule-list
     ;; Traverse / build output
     (rule '(program ??->define*))
     (rule '(define ?d ?vars (& ?blocks (?:*map ?lbl ?->block*)))
           (sub (define ?d
                  ~(apply merge-with #(or %1 %2) (filter map? block*))
                  ?blocks)))

     ;; Produce data for output
     (rule '(block ?lbl ??->stmt* ?tail)
           (apply merge-with #(or %1 %2) (filter map? stmt*)))
     (rule '(assign ?v ?e)
           (let [vt (::type (meta v))
                 et (::type (meta e))]
             (if (and vt et (not= vt et))
               {v {v vt e et}}
               {v (or vt et)})))))))
