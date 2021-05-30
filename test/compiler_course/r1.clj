(ns compiler-course.r1
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  var-locations with-allocated-registers]]
            [matches :refer [descend directed on-subexpressions rule rule-list rule-list! sub success]]
            [matches.types :refer [child-rules]]
            [clojure.string :as str]))

(def niceid (atom 0))

(defn gennice [sym]
  (symbol (str (name sym) \. (swap! niceid inc))))

(defn in [x env]
  (first (descend x env)))

;; Give every var a unique name

(def uniqify*
  (directed (rule-list [(rule '(let ([?x ?e]) ?body)
                              (let [x' (gennice x)
                                    env (assoc-in %env [:vars x] x')]
                                (sub (let ([?x' ~(in e env)])
                                       ~(in body env)))))
                        (rule '(if ?->e ?->then ?->else))
                        (rule '((? op symbol?) ?->a ?->b))
                        (rule '((? op symbol?) ?->a))
                        (rule '(? x symbol?) (get-in %env [:vars x]))])))

(defn uniqify [p]
  (reset! niceid 0)
  (uniqify* p))

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
     ;; TODO: if I had a breadth-first version of on-subexpressions I could do (not (< ...)) => (>= ...)
     (rule-list (rule '(eq? ?same ?same)
                      (when (immutable-expr? same)
                        true))
                (rule '(- ?a ?b) (sub (+ ?a (- ?b))))
                (rule '(or ?a ?b) (sub (if ?a true ?b)))
                (rule '(and ?a ?b) (sub (if ?a (if ?b true false) false)))
                (rule '(if ?exp ?same ?same)
                      (when (and (immutable-expr? exp)
                                 (immutable-expr? same))
                        (success same)))
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
     (rule-list (rule '((?:= let) ([?a ?->b]) ?->body))
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
                                 (if $maybe-not ?->then ?->else))
                      ;; preserve the not in (if (not ...) ...) because a future
                      ;; pass can eliminate the not by swapping the then/else
                      ;; order. It could also be done here but I'd need to do
                      ;; more work here and it's already done there...
                      (let [exp (preserve-not nots {:exp exp})]
                        (sub (if ?exp ?then ?else))))))))

(defn remove-complex-opera* [p]
  (rco-exp p))

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
  (letfn [(finalize-conditional [{:keys [finalized? pred? value then else] :as b}]
            (if finalized?
              b
              (if pred?
                ;; TODO: maybe the recursion here isn't required?
                (let [then (if (:pred? then) (finalize-conditional then) then)
                      else (if (:pred? else) (finalize-conditional else) else)]
                  (-> b
                      (update :b assoc
                              (:label then) (dissoc then :b)
                              (:label else) (dissoc else :b))
                      (update :b merge (:b then) (:b else))
                      (update :v (comp vec concat) (:v then) (:v else))
                      (update :s vec)
                      (dissoc :value :then :else)
                      (assoc :finalized? true)
                      (assoc :value (sub (if ?value (goto ~(:label then)) (goto ~(:label else)))))))
                ;; possible with (if true a b), return can be just {:value b}
                b)))]
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
                               (merge body
                                      {:b (merge (:b e) (:b body))
                                       :v (concat (:v e) [v] (:v body))
                                       :s (concat (:s e)
                                                  [(sub (assign ?v ~(:value e)))]
                                                  (:s body))})))
                       (rule '(if ?exp ?->then ?->else)
                             ;; Because this descends into the ->then and ->else
                             ;; expressions, the blocks they produce will be
                             ;; finalized twice if they are `if` exprs.
                             (explicate-pred exp (pred-env then else)))
                       (mapcat child-rules (child-rules explicate-expr)))))

(defn- add-block-return [{:keys [pred? value] :as b}]
  (if pred?
    b
    (assoc b :value (sub (return ?value)))))

(def explicate-control
  (rule '?p
        (let [p (explicate-tail p)
              ;; the above produces these blocks, too:
              blocks (reduce-kv (fn [blocks l b]
                                  (let [b (add-block-return b)]
                                    (assoc blocks l
                                           (sub (block ?l [~@(:v b)]
                                                       ~@(:s b)
                                                       ~(:value b))))))
                                {} (assoc (:b p) 'start p))]
           (sub (program [~@(:v p) ~@(mapcat :v (:vals (:b p)))]
                         ~blocks)))))

;; TODO: optimize-jumps, update select instructions
;; FIXME: do all blocks in explicate-* as continuation passing (not just the preds part)

;; Select instructions: rewrite as data representing X86 assembly

(def unv-rax
  "This is an annoying hack because I don't mark symbols as (v x) in an earlier
  pass, so I end up with (v (reg rax)) in my return clause. This cleans that
  up."
  (on-subexpressions (rule '(v (reg rax)) '(reg rax))))

(def select-inst-cond*
  (rule-list!
   (rule '((? op #{< eq?}) ?a ?b)
         (let [v (:v %env)
               flag ('{< l eq? e} op)]
           (sub [(cmpq ?b ?a)
                 (set ?flag (byte-reg al))
                 (movzbq (byte-reg al) ?v)])))
   (rule '(not ?->a)
         (let [v (:v %env)]
           (if (= v a)
             (sub [(xorq (int 1) ?v)])
             (sub [(movq ?a ?v)
                   (xorgq (int 1) ?v)]))))
   (rule '(v ?x)
         (sub [(movq (v ?x) ~(:v %env))]))))

(defn select-inst-cond [x env]
  (first (select-inst-cond* x env)))

(def select-instructions*
  ;; TODO: split to assign and tail versions.. See hints here
  ;; https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/lecture-Oct-6.html
  ;; TODO: remember to select instructions on each block
  (directed (rule-list! (rule '(program ?vars ?blocks)
                              (let [blocks (reduce-kv (fn [blocks l b]
                                                        (assoc blocks l (descend b)))
                                                      {} blocks)]
                                (sub (program ?vars ?blocks))))
                        (rule '(block ?label ?vars ??->instrs)
                              (sub (block ?label ?vars ~@(apply concat instrs))))
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
                        (rule '(assign ?x ((? op #{< eq?}) ?->a ?->b))
                              (let [x (sub (v ?x))]
                                (select-inst-cond (sub (?op ?a ?b)) {:v x})))
                        (rule '(assign ?x (not ?->a))
                              (let [x (sub (v ?x))]
                                (select-inst-cond (sub (not ?a)) {:v x})))
                        (rule '(assign ?x ?->a)
                              (let [x (sub (v ?x))]
                                (if (= x a)
                                  []
                                  (sub [(movq ?a ?x)]))))
                        (rule '(return ?x)
                              (concat (unv-rax
                                       (descend (sub (assign (reg rax) ?x))))
                                      ['(retq)]))

                        (rule '(if ((? cmp #{< eq?}) ?->a ?->b) (goto ?then) (goto ?else))
                              (sub [(cmpq ?b ?a)
                                    (jump ?cmp ?then)
                                    (jump true ?else)]))

                        (rule '(if ?->exp (goto ?then) (goto ?else))
                              (concat
                               (select-inst-cond exp {:v (sub (v ~(gennice 'tmp)))})
                               ;; FIXME: shouldn't it compare to 0 and go else? Seems like
                               ;; that would be a more expected semantic...
                               (sub [(cmpq (int 1) (v tmp))
                                     (jump eq? ?then)
                                     (jump true ?else)])))

                        (rule true '(int 1))
                        (rule false '(int 0))
                        (rule '(? i int?)
                              (sub (int ?i)))
                        (rule '(? v symbol?)
                              (sub (v ?v))))))

(defn select-instructions [x]
  (select-instructions* x))

(defn allocate-registers [prog]
  (let [g (to-graph (liveness prog))
        g (allocate-registers* g)
        var-locs (var-locations g)
        [_ vars blocks] prog
        blocks (-> (vec (vals blocks))
                   (with-allocated-registers {:loc var-locs}))]
    (sub (program ?var-locs ?blocks))))

(def remove-jumps
  (directed (rule-list (rule '(program ?var-locs [(?:* (& ?blocks ?->jumps))])
                             (let [blocks (reduce (fn [m [_ label :as b]]
                                                    (assoc m label b))
                                                  {} blocks)
                                   linear-jumps
                                   (->> (group-by second jumps)
                                        (filter #(= 1 (count (val %))))
                                        vals
                                        (apply concat)
                                        (into {}))
                                   blocks
                                   (reduce-kv (fn [blocks from to]
                                                (-> blocks
                                                    (update from (fn [b]
                                                                   (sub (~@(butlast b)
                                                                         ~@(drop 3 (blocks to))))))
                                                    (dissoc to)))
                                              blocks linear-jumps)]
                               (sub (program ?var-locs [~@(vals blocks)]))))
                       (rule '(block ?from ?vars ??i* (jump ?x ?to))
                             [from to])
                       (rule '(block ??x)
                             (success nil)))))



(def patch-instructions
  (directed (rule-list (rule '(program ?vars [??->blocks]))
                       (rule '(block ?label ?vars ??->i*)
                             (sub (block ?label ?vars ~@(apply concat i*))))
                       (rule '(addq (int 0) ?a) [])
                       (rule '(movq ?a ?a) [])
                       (rule '?x [x]))))

;; Stringify: Turn the data representing X86 assembly into actual assembly

(defn stack-var-max [var-locs]
  (->> (vals var-locs)
       (filter #(= 'stack (first %)))
       (map second)
       (apply max 0)))

(def caller-saved-registers (into #{} '[rax rcx rdx rsi rdi r8 r9 r10 r11]))
(def callee-saved-registers (into #{} '[rsp rbp rbx r12 r13 r14 r15]))

(defn save-registers* [var-locs]
  (->> (vals var-locs)
       (map second)
       distinct
       (filter callee-saved-registers)
       (map-indexed (fn [i reg]
                      (sub (movq (reg ?reg) (stack* ?i)))))
       vec))

(def save-registers
  (rule '(program ?var-locs ?blocks)
        (let [save-regs (save-registers* var-locs)]
          (sub (program ?var-locs ?save-regs ?blocks)))))

(defn stack-size [offset var-locs]
  (let [stack-vars (+ offset (stack-var-max var-locs))]
    (* 16 (max 1 (int (Math/ceil (/ stack-vars 2)))))))

(def stringify*
  (letfn [(fi [i*] (map #(str "    " % "\n") i*))]
    (directed (rule-list! (rule '(program ?var-locs [??->save-regs] ?blocks)
                                (let [offset (count save-regs)
                                      blocks (apply str (map #(first (descend % {:stack-offset offset}))
                                                             blocks))
                                      size (stack-size offset var-locs)]
                                  (str
                                   "    .globl main\n"
                                   blocks
                                   "main:\n"
                                   "    pushq %rbp\n"
                                   "    movq %rsp, %rbp\n"
                                   (apply str (fi save-regs))
                                   "    subq $" size ", %rsq\n"
                                   "    jmp start\n"
                                   "conclusion:\n"
                                   "    addq $" size ", %rsp\n"
                                   "    popq %rbp\n"
                                   "    retq\n")))
                          (rule '(block ?label ?vars ??->i*)
                                (apply str label ":\n" (fi i*)))
                          (rule '(jump true ?label)
                                (str "jmp " label))
                          (rule '(jump < ?label)
                                (str "jl " label))
                          (rule '(jump eq? ?label)
                                (str "je " label))
                          (rule '(callq read-int)
                                (str "callq read-int"))
                          (rule '(int ?i)
                                (str "$" i))
                          (rule '(deref ?v ?o)
                                (str o "(%" (name v) ")"))
                          (rule '(set ?x ?->y)
                                (str "set" x " " y))
                          (rule '(reg ?r)
                                (str "%" r))
                          (rule '(byte-reg ?r)
                                (str "%" r))
                          (rule '(stack* ?i)
                                (str (* -8 (inc i)) "(%rbp)"))
                          (rule '(stack ?i)
                                (str (* -8 (inc (+ (:stack-offset %env) i)))
                                     "(%rbp)"))
                          (rule '(retq)
                                "jmp conclusion")
                          (rule '(?x ?->a)
                                (str (name x) " " a))
                          (rule '(?x ?->a ?->b)
                                (str (name x) " " a ", " b))))))

(defn stringify [x]
  (stringify* x))

(def ->simple (comp #'remove-complex-opera* #'shrink #'uniqify))
(def ->flatten (comp #'explicate-control #'->simple))
(def ->select (comp #'select-instructions #'->flatten))
(def ->live (comp #'liveness #'->select))
(def ->alloc (comp #'allocate-registers #'->select))
(def ->jump (comp #'remove-jumps #'->alloc))
(def ->patch (comp #'patch-instructions #'->jump))
(def ->reg (comp #'save-registers #'->patch))
(def ->compile (comp str/split-lines
                     #(str/replace (with-out-str (println %)) #"\t" "    ")
                     #'stringify #'->reg))
