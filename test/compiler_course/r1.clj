(ns compiler-course.r1
  (:require [matches :refer [rule rule-list directed descend sub success on-subexpressions match]]
            [matches.nanopass.dialect :refer [=> ==> ===>]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]
            [matches.types :refer [child-rules]]))

(def niceid (atom 0))

(defn gennice [sym]
  (symbol (str (name sym) \. (swap! niceid inc))))

(defn in [x env]
  (first (descend x env)))

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
                        (rule '(+ ?->a ?->b))
                        (rule '(- ?->a))
                        (rule '(? x symbol?) (get-in %env [:vars x]))])))

;; Shrink the number of instructions we need to support (by expanding to equivalent expressions)

(def immutable-expr?*
  "If the expression is immutable, the result will be unmodified.
   If the expression is mutable, the result will be modified."
  (on-subexpressions
   ;; NOTE: all expressions that either mutate or read mutable data must be captured here:
   ;; NOTE: this isn't perfect because it doesn't distinguish (future) quoted expressions, but that could be added.
   (rule-list (rule '(read) (success nil))
              (rule '(vector-ref ??_) (success nil))
              (rule '(vector-set! ??_) (success nil)))))

(defn immutable-expr? [exp]
  (= exp (immutable-expr?* exp)))

(def shrink
  (let [preserve-order (fn [n a b expr]
                         (let [t (gennice n)]
                           (sub (let ([?t ?a])
                                  ~(expr t)))))]
    (on-subexpressions
     (rule-list (rule '(eq? ?same ?same)
                      (when (immutable-expr? same)
                        true))
                (rule '(- ?a ?b) (sub (+ ?a (- ?b))))
                ;; < is our canonical choice, so alter <= > >=
                (rule '(<= ?a ?b) (preserve-order 'le a b #(sub (not (< ?b ~%)))))
                (rule '(> ?a ?b) (preserve-order 'gt a b #(sub (< ?b ~%))))
                (rule '(>= ?a ?b) (sub (not (< ?a ?b))))))))

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
                (rule '((? op #{+ < eq?}) ?->a ?->b)
                      (wrap 'tmp+ a b (sub (?op ~(:value a) ~(:value b)))))
                (rule '((? op #{- not}) ?->a)
                      (wrap 'tmp- a nil (sub (?op ~(:value a)))))
                (rule '(read)
                      (wrap 'read nil nil '(read)))
                (rule '(not ?->e)
                      (wrap 'not e nil (sub (not ~(:value e)))))
                (rule '(? x int?)
                      {:value x})
                (rule '?x
                      {:value x})))))

(def rco-exp
  (let [preserve-not (comp first
                           (directed (rule-list (rule '(not ?->x))
                                                (rule '?_ (:exp %env)))))]
    (directed
     (rule-list (rule '(let ([?a ?->b]) ?->body))
                (rule '((? op #{+ < eq?}) ?a ?b)
                      (let [a (rco-atom a)
                            b (rco-atom b)]
                        ((:wrap a identity)
                         ((:wrap b identity)
                          (sub (?op ~(:value a) ~(:value b)))))))
                (rule '((? op #{- not}) ?a)
                      (let [a (rco-atom a)]
                        ((:wrap a identity)
                         (sub (?op ~(:value a))))))
                (rule '(?:letrec [maybe-not (?:as nots
                                                  (?:fresh [nots]
                                                           (| (not $maybe-not)
                                                              ?->exp)))]
                                 (if $maybe-not ?->then ?->else)))
                ;; preserve the not in (if (not ...) ...) because a future
                ;; pass can eliminate the not by swapping the then/else
                ;; order. It could also be done here but I'd need to do
                ;; more work here and it's already done there...
                (let [exp (preserve-not nots {:exp exp})]
                  (sub (if ?exp ?then ?else)))))))

(def remove-complex-operations
  (rule '(program ?p) (sub (program ~(rco-exp p)))))


;; Explicate expressions: remove nesting (aka flatten)

(def explicate-expr
  ;; NOTE these rules are also used in explicate-pred and -tail. Prefer updating the
  ;; returned block so that other keys it contains may pass through. (ie. pred?, then, else)
  ;; NOTE this is structured differently from the instructor's version so may need to be rewritten. In his
  ;; assign does not have a `value`, instead the var to be assigned to is passed in and every expression
  ;; creates the assign (I create the assign in the caller). I structure my return value as a block
  ;; and merge the blocks in the caller, but his passes the block in and merges them in place. The big
  ;; difference is that I work with a unified data structure while he works with multiple returns. Mine
  ;; seems better but maybe in the future his structure would be beneficial with more flexibility in
  ;; terms of what the statements within explicate-expr want to do with the
  ;; continuation. Also, mine doesn't seem to create trivial blocks? And... mine seems to nicely optimize out constant conditionals
  (directed (rule-list (rule '((?:= let) ([?v ?->e]) ?->body)
                             (-> body
                                 (merge (:b e))
                                 (assoc :v (concat (:v e) [v] (:v body))
                                        :s (concat (:s e)
                                                   [(sub (assign ?v ~(:value e)))]
                                                   (:s body)))))
                       (rule '(not ?->x)
                             (assoc x :value (sub (not ~(:value x)))))
                       (rule '?e
                             {:value e}))))

(defn pred-env [then else]
  ;; then/else may already have a label if their condition was a true/false
  ;; constant and they get pushed up the tree.
  {:then (assoc then :label (or (:label then) (gennice 'then)))
   :else (assoc else :label (or (:label else) (gennice 'else)))})

(def explicate-pred
  "Must always be called with an env containing {:then {...} :else {...}}"
  (letfn [(finalize-conditional [{:keys [pred? value then else] :as b}]
            (if pred?
              (let [then (if (:pred? then) (finalize-conditional then) then)
                    else (if (:pred? else) (finalize-conditional else) else)]
                (-> b
                    (update :b assoc
                            (:label then) (dissoc then :b)
                            (:label else) (dissoc else :b))
                    (update :b merge (:b then) (:b else))
                    (update :v (comp vec concat) (:v then) (:v else))
                    (update :s vec)
                    (dissoc :pred? :value :then :else)
                    (assoc :value (sub (if ?value (goto ~(:label then)) (goto ~(:label else)))))))
              ;; possible with (if true a b), return can be just {:value b}
              b))]
    (comp finalize-conditional
          first
          (directed
           (rule-list (rule '(if ?exp ?->then ?->else)
                            ;; ?then and ?else can use the existing env since they need the then/else blocks passed into explicate-pred.
                            ;; See https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/lecture-Sep-24.html
                            ;; That means they can just descend normally with -> (!!)
                            (in exp (pred-env then else)))
                      (rule '(not ?exp)
                            (in exp (assoc %env
                                           :then (:else %env)
                                           :else (:then %env))))
                      (rule true
                            (:then %env))
                      (rule false
                            (:else %env))
                      (rule '((? op #{< eq?}) ?a ?b)
                            (let [a (explicate-expr a)
                                  b (explicate-expr b)
                                  {:keys [then else]} %env]
                              {:v (concat (:v a) (:v b))
                               :s (concat (:s a) (:s b))
                               :b (merge (:b a) (:b b))
                               :pred? true
                               :value (sub (?op ~(:value a) ~(:value b)))
                               :then then
                               :else else}))
                      (rule '(? x symbol?)
                            (let [{:keys [then else]} %env]
                              {:pred? true :value x :then then :else else}))
                      (mapcat child-rules (child-rules explicate-expr)))))))

(def explicate-tail
  (directed (rule-list (rule '((?:= let) ([?v ?e]) ?->body)
                             (let [e (explicate-expr e)]
                               {:b (merge (:b e) (:b body))
                                :v (concat (:v e) [v] (:v body))
                                :s (concat (:s e)
                                           [(sub (assign ?v ~(:value e)))]
                                           (:s body))
                                :value (:value body)}))
                       (rule '(if ?exp ?->then ?->else)
                             (explicate-pred exp (pred-env then else)))
                       (mapcat child-rules (child-rules explicate-expr)))))

(def explicate-expressions
  (rule '(program ?p)
         (let [p (explicate-tail p)]
           (sub (program [[~@(:v p) ~@(mapcat :v (:vals (:b p)))]
                          ~(:b p)]
                         ~@(:s p)
                         (return ~(:value p)))))))

(comment
  (explicate-expressions
   (remove-complex-operations
    '(program (if (if (< x y)
                    (eq? (- x) (+ x (+ y 0)))
                    (eq? x 2))
                (+ y 2)
                (+ y 10)))))
  (explicate-expressions
   (remove-complex-operations
    '(program (if (if false
                    (eq? (- x) (+ x (+ y 0)))
                    (eq? x 2))
                (+ y 2)
                (+ y 10)))))
  (explicate-expressions
   (remove-complex-operations
    '(program (if false 1 2))))

  (explicate-expressions
   (remove-complex-operations
    (shrink
     '(program (if (if (if (eq? a a)
                         (> a b)
                         (> x y))
                     true
                     (eq? c 2))
                 (+ d 2)
                 (+ e 10))))))

  (do (reset! niceid 0)
      [(explicate-expressions
        (remove-complex-operations
         (shrink
          '(program (if (if (if (let ([z (> (+ 1 (- 1)) (+ 2 (- 2)))]) z)
                              (< x y)
                              (> x y))
                          (eq? (- x) (+ x (+ y 0)))
                          (eq? x 2))
                      (+ y 2)
                      (+ y 10))))))
       (reset! niceid 0)
       (explicate-expressions
        (remove-complex-operations
         (shrink
          '(program (if (if (if (> x y)
                              (< x y)
                              (> x y))
                          (eq? (- x) (+ x (+ y 0)))
                          (eq? x 2))
                      (+ y 2)
                      (+ y 10))))))])

  (explicate-expressions
   (remove-complex-operations
    (shrink
     '(program (not (< a b))))))

  (explicate-expressions
   (remove-complex-operations
    (shrink
     '(program (if (if (if (not (not false))
                         (< x y)
                         (> x y))
                     (eq? (- x) (+ x (+ y 0)))
                     (eq? x 2))
                 (+ y 2)
                 (+ y 10))))))

  ,)

;; TODO: optimize-jumps, update select instructions
;; FIXME: do all blocks in explicate-* as continuation passing (not just the preds part)

(def flatten
  (comp #'explicate-expressions #'remove-complex-operations))

;; Select instructions: rewrite as data representing X86 assembly

(def unv-rax
  "This is an annoying hack because I don't mark symbols as (v x) in an earlier
  pass, so I end up with (v (reg rax)) in my return clause. This cleans that
  up."
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

(def fu (comp #'flatten #'shrink #'uniqify))
(def sfu (comp #'select-instructions #'fu))
(def asfu (comp #'assign-homes #'sfu))
(def pasfu (comp #'patch-instructions #'asfu))
(def spasfu (comp println #'stringify #'pasfu))
