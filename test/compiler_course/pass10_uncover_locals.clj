(ns compiler-course.pass10-uncover-locals
  (:require
   [compiler-course.dialects :refer :all]
   [pattern :refer [=> dialects directed rule rule-list sub]]))


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
           (let [vt (:r1/type (meta v))
                 et (:r1/type (meta e))]
             (if (and vt et (not= vt et))
               {v {v vt e et}}
               {v (or vt et)})))))))
