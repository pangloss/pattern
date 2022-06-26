(ns compiler-course.pass15-patch-instructions
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



;; Remove copy to self, +/- 0 instructions

(def patch-instructions
  (dialects
   (=> RemoveUnallocated Patched)
   (directed (rule-list (rule '(program ??->define*))
                        (rule '(define ?d ?vars ?var-locs [??->block*]))
                        (rule '(block ?lbl ??->stmt* ?tail)
                              (sub (block ?lbl ~@(apply concat stmt*) ?tail)))
                        ;; traversal above, patches below
                        (rule '(addq (int 0) ?arg) [])
                        (rule '(subq (int 0) ?arg) [])
                        (rule '(movq ?arg ?arg) [])
                        (rule '(tailjmp ?arg)
                              (sub [(movq ?arg (reg rax))
                                    (tailjmp (reg rax))]))
                        ;; NOTE: not sure if this is required. Is callq *-104(%rbp) legal? If so remove this rule:
                        (rule '(indirect-callq ?arg)
                              (sub [(movq ?arg (reg rax))
                                    (indirect-callq (reg rax))]))
                        (rule '?x [x])))))
