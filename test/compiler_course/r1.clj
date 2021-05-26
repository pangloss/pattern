(ns compiler-course.r1
  (:require [matches :refer [rule rule-list directed descend sub success on-subexpressions match]]
            [matches.nanopass.dialect :refer [=> ==> ===>]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]))

(def niceid (atom 0))

(defn gennice [sym]
  (symbol (str (name sym) \. (swap! niceid inc))))

(defn in [x env]
  (first (descend x env)))

;; Shrink the number of instructions we need to support (by expanding to equivalent expressions)

(def shrink
  (let [preserve-order (fn [n a b expr]
                         (let [t (gennice n)]
                           (sub (let ([?t ?a])
                                  ~(expr t)))))]
    (on-subexpressions
     (rule-list (rule '(- ?a ?b) (sub (+ ?a (- ?b))))
                ;; < is our canonical choice, so alter <= > >=
                (rule '(<= ?a ?b) (preserve-order 'le a b #(sub (not (< ?b ~%)))))))))
                (rule '(> ?a ?b) (preserve-order 'gt a b #(sub (< ?b ~%))))
                (rule '(>= ?a ?b) (sub (not (< ?a ?b))))


;; Give every var a unique name


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


;; Remove complex operations

(declare rco-exp)

(def rco-atom
  (let [wrap (fn wrap [name a b exp]
               (let [t (gennice name)
                     a (:wrap a identity)
                     b (:wrap b identity)]
                 {:wrap (fn [r]
                          (a (b (sub (let ([?t ?exp])
                                       ?r)))))
                  :value t}))]
    (directed
     (rule-list (rule '(let ([?v ?e]) ?body)
                      (wrap 'let nil nil
                            (sub (let ([?v ~(rco-exp e)])
                                   ~(rco-exp body)))))
                (rule '(+ ?->a ?->b)
                      (wrap 'tmp+ a b (sub (+ ~(:value a) ~(:value b)))))
                (rule '(- ?->a)
                      (wrap 'tmp- a nil (sub (- ~(:value a)))))
                (rule '(read)
                      (wrap 'read nil nil '(read)))
                (rule '(? x int?)
                      {:value x})
                (rule '?x
                      {:value x})))))


(def rco-exp
  (directed
   (rule-list (rule '(let ([?a ?->b]) ?->body)
                    (success))
              (rule '(+ ?a ?b)
                    (let [a (rco-atom a)
                          b (rco-atom b)]
                      ((:wrap a identity)
                       ((:wrap b identity)
                        (sub (+ ~(:value a) ~(:value b)))))))
              (rule '(- ?a)
                    (let [a (rco-atom a)]
                      ((:wrap a identity)
                       (sub (- ~(:value a)))))))))

(def remove-complex-operations
  (rule '(program ?p) (sub (program ~(rco-exp p)))))

(rco-atom '(let ([x 10]) x))

(remove-complex-operations
 (uniqify
  '(program (let ([x 32]) (+ (let ([x 10]) x) x)))))


;; Explicate expressions: remove nesting (aka flatten)

(def explicate-assign
  (directed (rule-list (rule '(let ([?v ?->e]) ?->body)
                             {:v (concat (:v e) [v] (:v body))
                              :s (concat (:s e)
                                         [(sub (assign ?v ~(:value e)))]
                                         (:s body))
                              :value (:value body)})
                       (rule '?e
                             {:value e}))))

(def explicate-tail
  (directed (rule-list (rule '(let ([?v ?e]) ?->body)
                             (let [e (explicate-assign e)]
                               {:v (concat (:v e) [v] (:v body))
                                :s (concat (:s e)
                                           [(sub (assign ?v ~(:value e)))]
                                           (:s body))
                                :value (:value body)}))
                       (rule '?e {:value e}))))

(defn explicate-expressions [p]
  (match p
         '(program ?p)
         (let [p (explicate-tail p)]
           (sub (program [~@(:v p)]
                         ~@(:s p)
                         (return ~(:value p)))))))

(def flatten
  (comp #'explicate-expressions #'remove-complex-operations))

;; Select instructions: rewrite as data representing X86 assembly

(def unv-rax
  (on-subexpressions (rule '(v (reg rax)) '(reg rax))))


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
                       (rule '(return ?x)
                             (concat (unv-rax
                                      (descend (sub (assign (reg rax) ?x))))
                                     ['(retq)]))
                       (rule '(? i int?)
                             (sub (int ?i)))
                       (rule '(? v symbol?)
                             (sub (v ?v))))))

;; Assign homes and patch: This is a very basic and extremely suboptimal
;; allocation strategy since it puts everything on the stack.

(defn stack-size [var-count]
  (* 16 (max 1 (int (Math/ceil (/ (or var-count 0) 2))))))

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

(def patch-instruction
  (rule-list (rule '(?i (& ?a (deref ??_)) (& ?b (deref ??_)))
                   (sub [(movq ?a (reg rax))
                         (?i (reg rax) ?b)]))
             (rule '?x [x])))

(def patch-instructions
  (rule '(program ?size ?vars ??i*)
        (sub (program ?size ?vars
                      ~@(mapcat patch-instruction i*)))))

;; Stringify: Turn the data representing X86 assembly into actual assembly

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

(def fu (comp #'flatten #'uniqify))
(def sfu (comp #'select-instructions #'fu))
(def asfu (comp #'assign-homes #'sfu))
(def pasfu (comp #'patch-instructions #'asfu))
(def spasfu (comp println #'stringify #'pasfu))
