(ns compiler-course.pass06-add-types
  (:require
   [pattern :refer [=> dialects directed in rule rule-list sub subm success]]))


;; Add type metadata to everything possible

(defn tag [n]
  (cond (int? n) 'Integer
        (boolean? n) 'Boolean))

(def set-fn-type*
  (comp first
        (rule '(define (?n [?_ ?t*] ...) ?t ?_)
              (assoc-in %env [:type n] {:r1/type (sub (??t* -> ?t))}))))

;; TODO extract rule-fn into some composable features

(def add-types
  (dialects
   (=> Shrunk Typed)
   (letfn [(get-type [e]
             (select-keys (or (meta e) {:r1/type (tag e)})
                          [:r1/type]))]
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
                                           (assoc-in env [:type v] {:r1/type t}))
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
                        (subm (?op ??x* ?x) {:r1/type (tag true)})))
                 (rule '(call ?->e ??->e:args)
                       (success (subm (call ?e ??args)
                                      {:r1/type (last (:r1/type (get-type e)))})))
                 (rule '(funref ?v)
                       (subm (funref ?v)
                             (get-in %env [:type v])))
                 (rule '(read) (success (subm (read) {:r1/type (tag 1)})))
                 (rule '(void) (success (subm (void) {:r1/type 'Void})))
                 (rule '(global-value ?v:l)
                       (success (subm (global-value ?l) {:r1/type 'Integer})))
                 (rule '(collect ?i)
                       (success (subm (collect ?i) {:r1/type 'Void})))
                 (rule '(vector ??->e*)
                       (success (subm (vector ??e*)
                                      {:r1/type (sub (Vector ~@(map (comp :r1/type get-type) e*)))})))
                 (rule '(vector-ref ?->e:v ?->i)
                       (let [t (:r1/type (meta v))]
                         (if (and (sequential? t) (nth t (inc i) nil))
                           (success (subm (vector-ref ?v ?i)
                                          {:r1/type (nth t (inc i))}))
                           (sub (invalid-access (vector-ref ?v ?i) :r1/type ?t)))))
                 (rule '(vector-set! ??->e)
                       (success (subm (vector-set! ??e) {:r1/type 'Void})))
                 (rule '(allocate ?e:v ?type:t)
                       (success (subm (allocate ?v ?t) {:r1/type t})))
                 (rule '?v
                       (success (with-meta v (get-in %env [:type v])))))))))
