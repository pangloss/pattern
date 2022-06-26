(ns compiler-course.pass13-remove-unallocated
  (:require
   [pattern :refer [=> dialects on-subexpressions rule rule-list sub success]]))

;; Remove unallocated vars (if a var is set but never used)
;; This is not part of the instructor's compiler but seems good/simple. It falls
;; out because unused vars never get allocated to registers by my allocator so
;; they stay as (v ...). This could easily be part of patch-instructions.

(def remove-unallocated
  (dialects
   (=> RegAllocated RemoveUnallocated)
   (on-subexpressions
    (rule-list (rule '(movq ?arg0 (v ?v)) (success nil))
               (rule '(block ?lbl ??ins*)
                     (sub (block ?lbl ~@(remove nil? ins*))))))))
