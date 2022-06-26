(ns compiler-course.pass15-patch-instructions
  (:require
   [matches :refer [=> dialects directed rule rule-list sub]]))



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
