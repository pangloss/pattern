(ns compiler-course.pass06-add-types
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


;; Add type metadata to everything possible

(defn tag [n]
  (cond (int? n) 'Integer
        (boolean? n) 'Boolean))

(def set-fn-type*
  (comp first
        (rule '(define (?n [?_ ?t*] ...) ?t ?_)
              (assoc-in %env [:type n] {::type (sub (??t* -> ?t))}))))

;; TODO extract rule-fn into some composable features

(def add-types
  (dialects
   (=> Shrunk Typed)
   (letfn [(get-type [e]
             (select-keys (or (meta e) {::type (tag e)})
                          [::type]))]
     (directed
      ;; TODO: need a way to cleanly specify that I want the result meta merged with the input meta. Basically express:
      ;;
      ;; (success (with-meta ... (merge (meta (:rule/datum %env)) {... ...})))
      ;; ^ this is possible now via subm and subm!
      (rule-list (rule '(program ??d*)
                       (let [env (reduce (fn [env d] (set-fn-type* d env))
                                         %env d*)
                             d* (mapv #(in % env) d*)]
                         (success (sub (program ??d*)))))
                 (rule '(define (?v:n ??argdef*) ?type ?e)
                       (let [env (reduce (fn [env [v t]]
                                           (assoc-in env [:type v] {::type t}))
                                         %env argdef*)]
                         (sub (define (?n ??argdef*) ?type ~(in e env)))))
                 (rule '((?:= let) ([?v ?->e]) ?e:b)
                       (let [env (assoc-in %env [:type v] (get-type e))
                             v (in v env) ;; to simplify checking
                             b (in b env)]
                         (success (subm (let ([?v ?e]) ?b)
                                        (get-type b))
                                  env)))
                 (rule '((?:as op (| + - if)) ??->e:x* ?->e:x)
                       (success
                        (subm (?op ??x* ?x) (get-type x))))
                 (rule '((?:as op (| < eq? not)) ??->e:x* ?->e:x)
                       (success
                        (subm (?op ??x* ?x) {::type (tag true)})))
                 (rule '(call ?->e ??->e:args)
                       (success (subm (call ?e ??args)
                                      {::type (last (::type (get-type e)))})))
                 (rule '(funref ?v)
                       (subm (funref ?v)
                             (get-in %env [:type v])))
                 (rule '(read) (success (subm (read) {::type (tag 1)})))
                 (rule '(void) (success (subm (void) {::type 'Void})))
                 (rule '(global-value ?v:l)
                       (success (subm (global-value ?l) {::type 'Integer})))
                 (rule '(collect ?i)
                       (success (subm (collect ?i) {::type 'Void})))
                 (rule '(vector ??->e*)
                       (success (subm (vector ??e*)
                                      {::type (sub (Vector ~@(map (comp ::type get-type) e*)))})))
                 (rule '(vector-ref ?->e:v ?->i)
                       (let [t (::type (meta v))]
                         (if (and (sequential? t) (nth t (inc i) nil))
                           (success (subm (vector-ref ?v ?i)
                                          {::type (nth t (inc i))}))
                           (sub (invalid-access (vector-ref ?v ?i) ::type ?t)))))
                 (rule '(vector-set! ??->e)
                       (success (subm (vector-set! ??e) {::type 'Void})))
                 (rule '(allocate ?e:v ?type:t)
                       (success (subm (allocate ?v ?t) {::type t})))
                 (rule '?v
                       (success (with-meta v (get-in %env [:type v])))))))))
