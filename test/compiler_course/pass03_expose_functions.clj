(ns compiler-course.pass03-expose-functions
  (:require
   [compiler-course.dialects :refer :all]
   [pattern :refer [=> dialects directed in rule rule-list sub]]))

;; Find regular function calls and convert (f x) to ((funref f) x).

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
