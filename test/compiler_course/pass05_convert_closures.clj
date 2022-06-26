(ns compiler-course.pass05-convert-closures
  (:require
   [matches :refer [=> descend descend-all dialects directed gennice rule
                    rule-list sub success]]))

  ;; Convert closures

  ;; possible optimization: if a closure is not added to any data structure and is not returned from the block it's created in,
  ;; and if the total number of vars + free vars < 5 then I could treat the free vars as normal vars and call the closure as
  ;; a regular function call.
  ;; another optimization: after above, if the lambda has < 5 args, create the closure vector with space for the extra args and
  ;; at call time, just add those args to the vector. This wouldn't be thread safe because mutating a shared object.

(def convert-closures
  (dialects
   (=> Exposed Closures)
   (directed
    (rule-list (rule '(program ??define*)
                     (let [[defs {:keys [closures]}]
                           (reduce (fn [[def* env] d]
                                     (let [[d env] (descend d env)]
                                       [(conj def* d) env]))
                                   [[] {:closures [] :free-vars #{}}] define*)]
                       (sub (program ??defs ??closures))))
               (rule '(define (?v:n ??argdef*) ?type ?->e)
                     (let [_ (gennice '_)]
                       (sub (define (?n [?_ Closure] ??argdef*) ?type ?e))))
               (rule '(lambda (??argdef*) ?type ?e)
                     (let [[e {:keys [free-vars] :as env}] (descend e %env)
                           free-vars (apply disj free-vars (map first argdef*))
                           vars (vec free-vars)
                           ;; TODO get free-var types somehow...
                           n (gennice 'lambda)
                           carg (gennice 'carg)
                           e (reduce (fn [form [i v]]
                                       (sub (let ([?v (vector-ref ?carg ~(inc i))])
                                              ?form)))
                                     e (map-indexed vector vars))]
                       ;; I can use add-types to get expr types.
                       (success (sub (vector (funref ?n) ??free-vars))
                                (-> env
                                    (assoc :free-vars free-vars)
                                    (update :closures conj
                                            (sub (define (?n [?carg (Vector Closure (delay-type ??free-vars))] ;; FIXME
                                                             ??argdef*)
                                                   ?type
                                                   ?e)))))))
               (rule '((?:= let) ([?v ?e]) ?e:body)
                     (let [[e env] (descend e %env)
                           [body env] (descend body env)
                           env (update env :free-vars disj v)]
                       (success (sub (let ([?v ?e]) ?body))
                                env)))
               (rule '(call (funref ?v) ??e*)
                     (let [[e* env] (descend-all e* %env)]
                       (success (sub (call (funref ?v) (void) ??e*))
                                env)))
               (rule '(call ?e:f ??e*)
                     (let [[f env] (descend f %env)
                           closure (gennice 'closure)
                           [e* env] (descend-all e* env)]
                       (success (sub (let ([?closure ?f])
                                       (call (vector-ref ?closure 0) ?closure ??e*)))
                                env)))
               (rule '(funref ?v)
                     (sub (vector (funref ?v))))
               (rule '(?v ??e*)
                     (let [[e* env] (descend-all e* %env)]
                       (success (sub (?v ??e*))
                                env)))
               (rule '?v
                     (success v (update %env :free-vars conj v)))))))
