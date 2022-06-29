(ns compiler-course.pass08-remove-complex-opera
  (:require
   [compiler-course.dialects :refer :all]
   [compiler-course.pass07-expose-allocation :refer [m!]]
   [pattern :refer [=> dialects directed rule rule-list sub subm]]))

;; Remove complex operators / operands

(declare simplify-to-exp)

(def simplify-to-atom
  (dialects
   (=> Alloc Simplified)
   (let [wrap (fn wrap [name args exp]
                (let [t (gennice name)
                      w (reduce (fn [w arg]
                                  (comp w (:wrap arg identity)))
                                identity args)]
                  {:wrap (fn [r]
                           (w (sub (let ([?t ?exp])
                                     ?r))))
                   :value t}))]
     (directed
      (rule-list (rule '((?:= let) ([?v ?e]) ?e:body)
                       (wrap 'let nil
                             (subm (let ([?v ~(simplify-to-exp e)])
                                     ~(simplify-to-exp body))
                                   (m!))))
                 (rule '((? op #{+ < eq? - not}) ??->e:args)
                       (wrap (symbol (str (name op) ".tmp")) args
                             (subm (?op ~@(map :value args)) (m!))))
                 (rule '(call ??->guts)
                       (wrap 'call guts (subm (call ~@(map :value guts)) (m!))))
                 (rule '(funref ?v)
                       (wrap 'funref nil (subm (funref ?v) (m!))))
                 (rule '(read)
                       (wrap 'read nil
                             (with-meta '(read) {:r1/type 'Integer})))
                 (rule '(global-value ?name)
                       (wrap name nil (:rule/datum %env)))
                 (rule '(vector-ref ?->e:v ?i)
                       (wrap (symbol (str "vec+" i)) [v]
                             (subm (vector-ref ~(:value v) ?i) (m!))))
                 (rule '(vector-set! ?->e:v ?i ?->e)
                       (wrap (symbol (str "vec+" i)) [v e]
                             (subm (vector-set! ~(:value v) ?i ~(:value e)) (m!))))
                 (rule '(not ?->e)
                       (wrap 'not [e]
                             (subm (not ~(:value e)) (m!))))
                 (rule '?i
                       {:value i})
                 (rule '?other
                       {:value other}))))))

(defmacro simplify-to-atoms [vars subm-exp]
  ;; This macro captures the subm in source state before the resulting structure
  ;; is assembled. By re-binding the args symbol (~vars) used by the subm
  ;; expression, it can change the contents of the result to the simplified
  ;; expression. Then it wraps it in all of the wrappers via the composed wrap
  ;; function.
  `(let [r# (reduce (fn [r# exp#]
                      (let [x# (simplify-to-atom exp#)
                            wrap# (:wrap x#)
                            r# (update r# :values conj (:value x#))]
                        (if wrap#
                          ;; compose in reverse
                          (assoc r# :wrap (comp (:wrap r#) wrap#))
                          r#)))
                    {:wrap identity :values []} ~vars)
         wrap# (:wrap r#)
         ;; vars is just a symbol:
         ~vars (:values r#)]
     (wrap# ~subm-exp)))

(def simplify-to-exp
  (dialects
   (=> Alloc Simplified)
   (let [preserve-not (comp first
                            (directed (rule-list (rule '(not ?->e:x))
                                                 (rule '?_ (:exp %env)))))]
     (directed
      (rule-list (rule '(program ??->define*))
                 (rule '(define ??etc ?->e))
                 (rule '((?:= let) ([?v:a ?->e:b]) ?->e:body))
                 (rule '((? op #{vector-set! + < eq? vector-ref - not global-value})
                         ??e:args)
                       (simplify-to-atoms args (subm (?op ??args) (m!))))
                 (rule '(call ??guts)
                       (simplify-to-atoms guts (subm (call ??guts) (m!))))
                 (rule '(?:letrec [maybe-not (?:as nots
                                                   (?:fresh [nots]
                                                            (| (not $maybe-not)
                                                               ?->e:exp)))]
                                  (if $maybe-not ?->e:then ?->e:else))
                       ;; preserve the not in (if (not ...) ...) because a future
                       ;; pass can eliminate the not by swapping the then/else
                       ;; order. It could also be done here but I'd need to do
                       ;; more work here and it's already done there...
                       ;; FIXME? what about (if (let ...) ...)?
                       (let [exp (preserve-not nots {:exp exp})]
                         (subm (if ?exp ?then ?else) (m!)))))))))

(defn remove-complex-opera*
  "Remove complex operators/operands by let binding them around any complex expression."
  {:=>/from 'Alloc  :=>/to 'Simplified}
  [p]
  (simplify-to-exp p))
