(ns compiler-course.pass03-expose-functions
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


(def expose-functions
  (dialects
   (=> Shrunk Exposed)
   (directed
    (rule-list
     (rule '(program (define (?v:defs ??argdef*) ?type ?e) ...)
           (let [env {:defs (set defs)}
                 e (mapv #(in % env) e)]
             (sub (program (define (?defs ??argdef*) ?type ?e) ...))))
     (rule '(dialect ?def ?type ?->e))
     (rule '(if ??->e))
     (rule '((?:= let) ([?v ?->e]) ?e:body)
           (sub (let ([?v ?e])
                  ~(in body (update %env :defs disj v)))))
     (rule '(?op ??->e))
     (rule '?v
           (when (get-in %env [:defs v])
             (sub (funref ?v))))))))
