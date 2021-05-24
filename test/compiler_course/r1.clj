(ns compiler-course.r1
  (:require [matches :refer [rule rule-list directed descend sub success on-subexpressions]]
            [matches.nanopass.dialect :refer [=> ==> ===>]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]))

(defpass interp-exp nil
  (let-rulefn [(Expr nil
                     [(rule '(Int ?n)
                            n)
                      (rule '(Prim read)
                            (let [r (read)]
                              (when (int? r) r)))
                      (rule '(Prim - ?->e)
                            (- e))
                      (rule '(Prim + (?->e1 ?->e2))
                            (+ e1 e2))])]
    ;; FIXME: doesn't work without either <> part or a return value... %pass doesn't work
    Expr))

(interp-exp '(Prim - (Prim + ((Int 2) (Int 99)))))

(defn in [x env]
  (first (descend x env)))

;; Exercise 2:
;;
#_ ;; FIXME: this should work but (success) fails.
(def uniqify
  (directed (rule-list [(rule '(let ([?x ?e]) ?body)
                              (let [x' (gensym x)
                                    env (assoc-in %env [:vars x] x')]
                                (sub (let ([?x' ~(in e env)])
                                       ~(in body env)))))
                        (rule '(+ ?->a ?->b) (success))
                        (rule '(- ?->a) (success))
                        (rule '(? x symbol?)
                              (get-in %env [:vars x]))])))

(def uniqify
  (directed (rule-list (rule '(program ?->p) (sub (program ?p)))
                       (rule '(let ([?x ?e]) ?body)
                             (let [x' (gensym x)
                                   env (assoc-in %env [:vars x] x')]
                               (sub (let ([?x' ~(in e env)])
                                      ~(in body env)))))
                       (rule '(+ ?->a ?->b) (sub (+ ?a ?b)))
                       (rule '(- ?->a) (sub (- ?a)))
                       (rule '(? x symbol?) (get-in %env [:vars x])))))

(comment
  (uniqify '(program (let ([x 32]) (+ (let ([x 10]) x) x))))
  (uniqify '(program (let ([x 32]) (+ 10 x)))))

(def flatten
  (directed (rule-list (rule '(program ?->p)
                             (sub (program (~@(distinct (:v p)))
                                           ~@(:s p)
                                           (return ~(:value p)))))
                       (rule '(let ([?x ?->e]) ?->body)
                             {:v (concat (:v e) [x] (:v body))
                              :s (concat (:s e)
                                         [(sub (assign ?x ~(:value e)))]
                                         (:s body))
                              :value (:value body)})
                       (rule '(+ ?->a ?->b)
                             (let [t (gensym 'tmp+)]
                               {:v (concat (:v a) (:v b) [t])
                                :s (concat (:s a) (:s b)
                                           [(sub (assign ?t (+ ~(:value a) ~(:value b))))])
                                :value t}))
                       (rule '(- ?->a)
                             (let [t (gensym 'tmp-)]
                               {:v (concat (:v a) [t])
                                :s (concat (:s a) [(sub (assign ?t (- ~(:value a))))])
                                :value t}))
                       (rule '(read)
                             (let [t (gensym 'read)]
                               {:v [t]
                                :s [(sub (assign ?t (read)))]
                                :value t}))
                       (rule '?x {:value x}))))

(def fu (comp #'flatten #'uniqify))

(comment
  (flatten (uniqify '(program (let ([x 32]) (+ (let ([x 10]) x) x)))))
  (fu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (fu '(program (let ([a 42])
                  (let ([b a])
                    b))))

  (fu '(program (let ([a 42])
                  (let ([b a])
                    b))))

  (fu '(program (let ([x 32]) (+ 10 x)))))


(def select-instructions
  (directed (rule-list (rule '(program ?vars ??->instrs)
                             (sub (program ?vars ~@(apply concat instrs))))
                       (rule '(assign ?x (+ ?->a ?->b))
                             (sub [(movq ?a (var ?x))
                                   (addq ?b (var ?x))]))
                       (rule '(assign ?x (read))
                             (sub [(callq read-int)
                                   (movq (reg rax) (var ?x))]))
                       (rule '(assign ?x (- ?->a))
                             (sub [(movq ?a (var ?x))
                                   (negq (var ?x))]))
                       (rule '(assign ?x ?->a)
                             (sub [(movq ?a (var ?x))]))
                       (rule '(return ?->x)
                             (sub [(return ?x)]))
                       (rule '(? i int?)
                             (sub (int ?i)))
                       (rule '(? v symbol?)
                             (sub (var ?v))))))

(def sfu (comp #'select-instructions #'flatten #'uniqify))

(comment
  (sfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

  (sfu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (sfu '(program (let ([a 42])
                  (let ([b a])
                    b))))

  [(fu '(program (let ([x 32]) (+ (- 10) x))))
   (sfu '(program (let ([x 32]) (+ (- 10) x))))]
  ,)

(def assign-homes
  (directed (rule-list (rule '(program ?vars ??->i*)
                             (sub (program ~(* 16 (max 1 (int (Math/ceil (/ (:var-count %env 0) 2)))))
                                           ?vars ??i*)))
                       (on-subexpressions
                        (rule '(var ?x)
                              (let [offset (get-in %env [:offset x])
                                    found offset
                                    offset (or offset (* -8 (inc (:var-count %env 0))))
                                    env (if found
                                          %env
                                          (-> %env
                                              (update :var-count (fnil inc 0))
                                              (assoc-in [:offset x] offset)))]
                                (success (sub (deref rbp ?offset))
                                         env)))))))

(def asfu (comp #'assign-homes #'sfu))

(comment
  (asfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

  (asfu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (asfu '(program (let ([a 42])
                    (let ([b a])
                      b))))

  [(fu '(program (let ([x 32]) (+ (- 10) x))))
   (sfu '(program (let ([x 32]) (+ (- 10) x))))
   (asfu '(program (let ([x 32]) (+ (- 10) x))))]
  ,)

(def patch-instruction
  (rule-list (rule '(?i (& ?a (deref ??_)) (& ?b (deref ??_)))
                   (sub [(movq ?a (reg rax))
                         (?i (reg rax) ?b)]))
             (rule '?x [x])))

(def patch-instructions
  (rule '(program ?size ?vars ??i*)
        (sub (program ?size ?vars
                      ~@(mapcat patch-instruction i*)))))

(def pasfu (comp #'patch-instructions #'asfu))

(comment
  (pasfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

  (pasfu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (pasfu '(program (let ([a 42])
                    (let ([b a])
                      b))))

  [(fu '(program (let ([x 32]) (+ (- 10) x))))
   (sfu '(program (let ([x 32]) (+ (- 10) x))))
   (asfu '(program (let ([x 32]) (+ (- 10) x))))
   (pasfu '(program (let ([x 32]) (+ (- 10) x))))]
  ,)
