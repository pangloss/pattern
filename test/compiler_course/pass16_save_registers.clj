(ns compiler-course.pass16-save-registers
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


;; Capture callee-save registers on entry and restore them on exit

(defn save-registers* [var-locs]
  (->> (vals var-locs)
       (map second)
       distinct
       (filter callee-saved-registers)
       (map-indexed (fn [i reg]
                      (sub (movq (reg ?reg) (stack* ?i)))))
       vec))

(def save-registers
  (dialects
   (=> Patched Patched+)
   (directed
    (rule-list
     (rule '(program ??->define*))
     (rule '(define ?d ?vars ?var-locs ?block*)
           (let [save-regs (save-registers* var-locs)]
             (sub (define ?d ?vars ?var-locs ?save-regs ?block*))))))))
