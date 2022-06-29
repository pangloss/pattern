(ns compiler-course.pass16-save-registers
  (:require
   [compiler-course.dialects :refer :all]
   [compiler-course.r1-allocator :refer [callee-saved-registers]]
   [pattern :refer [=> dialects directed rule rule-list sub]]))


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
