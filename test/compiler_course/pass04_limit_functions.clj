(ns compiler-course.pass04-limit-functions
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



;; Functions must not have more than 6 args. Stuff the remaining in a vector.

(def args->vector-ref
  (directed
   (rule-list (rule '(let ([?v ?->e]) ?e:body)
                    (sub (let ([?v ?e])
                           ~(in body (update %env :argid dissoc v)))))
              (rule '(call ?f ??->e))
              (rule '((? op ~r1-keyword?) ??->e))
              (rule '?v
                    (when-let [pos (get-in %env [:argid v])]
                      (sub (vector-ref ~(:vector %env) ?pos)))))))

(def limit-functions
  (dialects
   (=> Exposed Exposed)
   (on-subexpressions
    (rule-list
     (rule '(define (?v ??argdef*) ?type ?body)
           (when (< 6 (count argdef*))
             (let [[args tail] (split-at 5 argdef*)
                   tv (gennice 'arg-tail)
                   tt (map second tail)
                   body (-> body
                            (args->vector-ref {:vector tv
                                               :argid (zipmap (map first tail) (range))})
                            first)]
               (sub (define (?v ??args [?tv (Vector ??tt)]) ?type ?body)))))
     (rule '(call ?e ??e:args)
           (when (< 6 (count args))
             (let [[args tail] (split-at 5 args)]
               (sub (call ?e ??args (vector ??tail))))))))))
