(ns compiler-course.pass13-remove-unallocated
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
