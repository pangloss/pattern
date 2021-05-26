(ns compiler-course.r1
  (:require [matches :refer [rule rule-list directed descend sub success on-subexpressions]]
            [matches.nanopass.dialect :refer [=> ==> ===>]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]))

(def niceid (atom 0))

(defn gennice [sym]
  (symbol (str (name sym) \. (swap! niceid inc))))

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

;; Ok... my version seems to have full functionality and it's a LOT more concise
;; and understandable than the instructor version posted here:
;; https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/lecture-Sep-8.html.
;;
;; On the other hand I think mine is not quite as explicit as his. He seems to
;; have clearly defined languages step-by-step, anticipating the nanopass style,
;; while I stayed with a sort of progressively simplified version of "racket" as
;; the syntax. He quickly moves from (let ([x y]) e) to (Let x y e), for
;; instance.

;; Exercise 2:
;;
(def uniqify
  (directed (rule-list [(rule '(program ?p)
                              (do
                                (reset! niceid 0)
                                (sub (program ~(descend p)))))
                        (rule '(let ([?x ?e]) ?body)
                              (let [x' (gennice x)
                                    env (assoc-in %env [:vars x] x')]
                                (sub (let ([?x' ~(in e env)])
                                       ~(in body env)))))
                        (rule '(+ ?->a ?->b) (success))
                        (rule '(- ?->a) (success))
                        (rule '(? x symbol?) (get-in %env [:vars x]))])))

(defn- rco-atom-wrap [name a b exp]
  (let [t (gennice name)
        a (:wrap a identity)
        b (:wrap b identity)]
    {:wrap (fn [r]
             (a (b (sub (let ([?t ?exp])
                          ?r)))))
     :value t}))

(def rco-atom*
  (directed
   (rule-list (rule '(+ ?->a ?->b)
                    (rco-atom-wrap 'tmp+ a b (sub (+ ~(:value a) ~(:value b)))))
              (rule '(- ?->a)
                    (rco-atom-wrap 'tmp- a nil (sub (- ~(:value a)))))
              (rule '(read)
                    (rco-atom-wrap 'read nil nil '(read)))
              #_ ;; this was a thought experiment. let stametments may contain expressions.
              (rule '(let ([?v ?->e]) ?->body)
                    (let [t (gennice 'let)]
                      {:wrap (fn [r]
                               (let [w (:wrap body)]
                                 ((:wrap e identity)
                                  (sub (let ([?v ~(:value e)])
                                         ~(if w
                                            (w (sub (let ([?t ~(:value body)])
                                                      ?r)))
                                            (:value body)))))))
                       :value t}))
              (rule '(? x int?)
                    {:value x})
              (rule '?x
                    {:value x}))))

(defn rco-atom [exp]
  (let [{:keys [wrap value] :or {wrap identity}} (rco-atom* exp)]
    (wrap value)))

(def rco-exp
  (directed
   (rule-list (rule '(let ([?a ?->b]) ?->body)
                    (success))
              (rule '(+ ?a ?b)
                    (let [a (rco-atom* a)
                          b (rco-atom* b)]
                      ((:wrap a identity)
                       ((:wrap b identity)
                        (sub (+ ~(:value a) ~(:value b)))))))
              (rule '(- ?a)
                    (let [a (rco-atom* a)]
                      ((:wrap a identity)
                       (sub (- ~(:value a)))))))))

(def remove-complex-operations
  (directed (rule-list (rule '(program ?->p) (success))
                       rco-exp)))

(remove-complex-operations '(program (- (- x))))
(rco-atom '(let ([x (+ (+ 0 1) (- 2))]) x))
(rco-atom '(- x))



;; In the lecture notes this was 2 passes: remove-complex-opera* and
;; explicate-control, but this pass was not complex anyway... so that seems not
;; too valuable. Perhaps in a more complete language the pain would become
;; apparent?
;;
;; Yes, in the R2 language, this is extended in a way that I think will make their approach superior so I'm rewriting it.
;;
;; The racket version uses multiple returns, but returning a dictionary
;; accomplishes the same thing and I think this is a lot more comprehensible.
;;
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
                             (let [t (gennice 'tmp+)]
                               {:v (concat (:v a) (:v b) [t])
                                :s (concat (:s a) (:s b)
                                           [(sub (assign ?t (+ ~(:value a) ~(:value b))))])
                                :value t}))
                       (rule '(- ?->a)
                             (let [t (gennice 'tmp-)]
                               {:v (concat (:v a) [t])
                                :s (concat (:s a) [(sub (assign ?t (- ~(:value a))))])
                                :value t}))
                       (rule '(read)
                             (let [t (gennice 'read)]
                               {:v [t]
                                :s [(sub (assign ?t (read)))]
                                :value t}))
                       (rule '?x {:value x}))))

(def fu (comp #'flatten #'uniqify))

(def select-instructions
  (directed (rule-list (rule '(program ?vars ??->instrs)
                             (sub (program ?vars ~@(apply concat instrs))))
                       (rule '(assign ?x (+ ?->a ?->b))
                             (let [x (sub (v ?x))]
                               (cond (= x b) (sub [(addq ?a ?b)])
                                     (= x a) (sub [(addq ?b ?a)])
                                     :else (sub [(movq ?a ?x)
                                                 (addq ?b ?x)]))))
                       (rule '(assign ?x (read))
                             (let [x (sub (v ?x))]
                               (sub [(callq read-int)
                                     (movq (reg rax) ?x)])))
                       (rule '(assign ?x (- ?->a))
                             (let [x (sub (v ?x))]
                               (if (= x a)
                                 (sub [(negq ?x)])
                                 (sub [(movq ?a ?x)
                                       (negq ?x)]))))
                       (rule '(assign ?x ?->a)
                             (let [x (sub (v ?x))]
                               (if (= x a)
                                 []
                                 (sub [(movq ?a ?x)]))))
                       (rule '(return ?->x)
                             (sub [(movq ?x (reg rax))
                                   (retq)]))
                       (rule '(? i int?)
                             (sub (int ?i)))
                       (rule '(? v symbol?)
                             (sub (v ?v))))))

(def sfu (comp #'select-instructions #'flatten #'uniqify))


(defn stack-size [var-count]
  (* 16 (max 1 (int (Math/ceil (/ (or var-count 0) 2))))))

;; This is a very basic and extremely suboptimal allocation strategy since it puts everything on the stack.
(def assign-homes
  (directed (rule-list (rule '(program ?vars ??->i*)
                             (sub (program ~(stack-size (:var-count %env 0))
                                           ?vars ??i*)))
                       (on-subexpressions
                        (rule '(v ?x)
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

(def stringify
  (directed (rule-list (rule '(program ?size ?vars ??->i*)
                             (str
                              "start:\n"
                              (apply str (map #(str "\t" % "\n") i*))
                              "\tjmp conclusion\n"
                              "\t.globl main\n"
                              "main:\n"
                              "\tpushq %rbp\n"
                              "\tmovq %rsp, %rbp\n"
                              "\tsubq $" size ", %rsq\n"
                              "\tjmp start\n"
                              "conclusion:\n"
                              "\taddq $" size ", %rsp\n"
                              "\tpopq %rbp\n"
                              "\tretq\n"))
                       (rule '(int ?i)
                             (str "$" i))
                       (rule '(deref ?v ?o)
                             (str o "(%" (name v) ")"))
                       (rule '(reg ?r)
                             (str "%" r))
                       (rule '(ret) "")
                       (rule '(?x)
                             (name x))
                       (rule '(?x ?->a)
                             (str (name x) " " a))
                       (rule '(?x ?->a ?->b)
                             (str (name x) " " a ", " b)))))

(def spasfu (comp println #'stringify #'pasfu))


(comment
  [(uniqify '(program (let ([x 32]) (+ (let ([x 10]) x) x))))]

  [(uniqify '(program (let ([x 32]) (+ 10 x))))]

  ,
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

  (fu '(program (let ([x 32]) (+ 10 x))))

  (sfu '(program (let ([x 32]) (+ (let ([x (- 10)]) x) x))))

  (sfu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (sfu '(program (let ([a 42])
                   (let ([b a])
                     b))))

  [(fu '(program (let ([x 32]) (+ (- 10) x))))
   (sfu '(program (let ([x 32]) (+ (- 10) x))))]
  ,
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
  ,
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
  ,
  (spasfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

  (spasfu
   '(program
     (let ([x (+ (- (read)) 11)])
       (+ x 41))))

  (spasfu '(program (let ([a 42])
                      (let ([b a])
                        b))))

  [(fu '(program (let ([x 32]) (+ (- 10) x))))
   (sfu '(program (let ([x 32]) (+ (- 10) x))))
   (asfu '(program (let ([x 32]) (+ (- 10) x))))
   (pasfu '(program (let ([x 32]) (+ (- 10) x))))
   (spasfu '(program (let ([x 32]) (+ (- 10) x))))]
  ,)
