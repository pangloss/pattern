(ns compiler-course.pass01-uniqify
  (:require
   [matches :refer [=> dialects directed gennice in niceid rule rule-list sub]]))


;; Give every var a unique name

(def uniqify*
  (dialects
   (=> R1 R1Fun)
   (directed (rule-list [(rule '(define (?v [?v* ?type*] ...) ?type ?e)
                               (let [[v'* env] (reduce (fn [[v'* env] x]
                                                         (let [x' (gennice x)]
                                                           [(conj v'* x') (assoc-in env [:vars x] x')]))
                                                       [[] %env]
                                                       v*)
                                     e (in e env)]
                                 (sub (define (?v [?v'* ?type*] ...) ?type ?e))))
                         ;; add special rules here for shadowing if / let if I want, then shadowed if -> if.5 and it's easy
                         ;; everything else is already covered.
                         (rule '((?:= let) ([?v:x ?e]) ?e:body)
                               (let [x' (gennice x)
                                     env (assoc-in %env [:vars x] x')]
                                 (sub (let ([?x' ~(in e env)])
                                        ~(in body env)))))
                         (rule '(if ?->e ?->e:then ?->e:else))
                         (rule '(lambda (??argdef*) ?type ?->e))
                         (rule '(??->forms))
                         (rule '?v (get-in %env [:vars v]))]))))

(def uniqify-and-shrink-rfun*
  (rule-list
   (rule '[(define (?v ??argdef*) ??more) ... ?e]
         (let [[defs env] (reduce (fn [[defs env] [v argdef* more]]
                                    (let [v' (gennice v)]
                                      [(conj defs (sub (define (?v' ??argdef*) ??more)))
                                       (assoc-in env [:vars v] v')]))
                                  [[] {}] (map vector v argdef* more))
               defs (mapv #(first (uniqify* % env)) defs)
               main (first (uniqify* (sub (define (main) Integer ?e)) env))
               defs (conj defs main)]
           (sub (program ??defs))))
   (rule '?e
         (let [main (uniqify* (sub (define (main) Integer ?e)))]
           (sub (program ?main))))))

(defn uniqify
  {:=>/from 'R1 :=>/to 'R1Fun}
  [p]
  (reset! niceid 0)
  (uniqify-and-shrink-rfun* p))
