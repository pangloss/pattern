(ns compiler-course.r1
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  var-locations with-allocated-registers]]
            [matches :refer [descend directed on-subexpressions rule rule-list rule-list! sub success subm rule-simplifier]]
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

(defn tag [n]
  (cond (int? n) 'Integer
        (boolean? n) 'Boolean))

(def add-types
  (letfn [(get-type [e]
            (or (meta e) {:type (tag e)}))]
    (directed
     (rule-list (rule '((?:= let) ([?v ?->e]) ?b)
                      (let [env (assoc-in %env [:type v] (get-type e))
                            v (first (descend v env)) ;; to simplify checking
                            b (first (descend b env))]
                        (success (subm (let ([?v ?e]) ?b)
                                       (get-type b))
                                 env)))
                (rule '((?:as op (| + - if)) ??->x* ?->x)
                      (success
                       (subm (?op ??x* ?x) (get-type x))))
                (rule '((?:as op (| < eq? not)) ??->x* ?->x)
                      (success
                       (subm (?op ??x* ?x) {:type (tag true)})))
                (rule '(read) (success (subm (read) {:type (tag 1)})))
                (rule '(void) (success (subm (void) {:type 'Void})))
                (rule '(vector ??->e*)
                      (success (subm (vector ??e*)
                                     {:type (sub (Vector ~@(map (comp :type get-type) e*)))})))
                (rule '(vector-ref ?->v ?->i)
                      (success (subm (vector-ref ?v ?i)
                                     {:type (nth (:type (meta v))
                                                 (inc i))})))
                (rule '(vector-set! ??->e)
                      (success (subm (vector-set! ??e) {:type 'Void})))
                (rule '(? s symbol?)
                      (success (with-meta s (get-in %env [:type s]))))))))

(def expose-allocation
  (rule-simplifier
   (rule '(vector ??e*)
         (sub (vector> ~(:type (meta (:rule/datum %env))) [] ??e*)))
   (rule '(vector> ?type ?names ?e ??e*)
         (let [n (gennice 'vec)
               ;; building names in reverse
               names (conj names n)]
           (sub (let ([?n ?e])
                  (vector> ?type ?names ??e*)))))
   (rule '(vector> ?type ?names)
         (let [len (count names)
               v (gennice 'vector)
               _ (gennice '_)
               bytes (inc len)]
           (sub
            (let ([?_ (if (< (+ (global-value free_ptr) ?bytes)
                             (global-value fromspace_end))
                        (void)
                        (collect ?bytes))])
              (let ([?v (allocate ?len ?type)])
                (vector< ?v ?names))))))
   (rule '(vector< ?v [??n* ?n])
         ;; using names in reverse, so n* count is the vector position
         (let [idx (count n*)
               _ (gennice '_)]
           (sub (let ([?_ (vector-set! ?v ?idx ?n)])
                  (vector< ?v [??n*])))))
   (rule '(vector< ?v [])
         v)))

(comment
  (reset! niceid 0)
  (expose-allocation (sub (+ 1 ~(subm (vector 1 2) {:type (sub (Vector ~(tag 1) ~(tag 1)))})))))


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
                ;; TODO: refactor this with hard-coded fn names and arities
                (rule '((? op #{+ < eq?}) ?->a ?->b)
                      (wrap 'tmp+ a b (sub (?op ~(:value a) ~(:value b)))))
                (rule '((? op #{- not}) ?->a)
                      (wrap 'tmp- a nil (sub (?op ~(:value a)))))
                (rule '(read)
                      (wrap 'read nil nil '(read)))
                (rule '(global-value ?name)
                      (wrap name nil nil (:rule/datum %env)))
                (rule '(vector-ref ?->v ?i)
                      (wrap (symbol (str "vec+" i)) v nil (sub (vector-ref ~(:value v) ?i))))
                (rule '(vector-set! ?->v ?i ?->e)
                      (wrap (symbol (str "vec+" i)) v e (sub (vector-set! ~(:value v) ?i ~(:value e)))))
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
                ;; TODO: refactor this with hard-coded fn names and arities
                (rule '((? op #{vector-set!}) ?a ?b ?c)
                      (let [a (rco-atom a)
                            b (rco-atom b)
                            c (rco-atom c)]
                        ((:wrap a identity)
                         ((:wrap b identity)
                          ((:wrap c identity)
                           (sub (?op ~(:value a) ~(:value b) ~(:value c))))))))
                (rule '((? op #{+ < eq? vector-ref}) ?a ?b)
                      (let [a (rco-atom a)
                            b (rco-atom b)]
                        ((:wrap a identity)
                         ((:wrap b identity)
                          (sub (?op ~(:value a) ~(:value b)))))))
                (rule '((? op #{- not global-value}) ?a)
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
                      ;; FIXME? what about (if (let ...) ...)?
                      (let [exp (preserve-not nots {:exp exp})]
                        (sub (if ?exp ?then ?else))))))))

(defn remove-complex-opera* [p]
  (rco-exp p))

;; Explicate expressions: remove nesting (aka flatten)

(declare x-pred)

(let [x-assign*
      (rule-list
       (rule '(if ?e ?then ?else)
             (let [then (x-assign (:var %env) then (:cont %env))
                   else (x-assign (:var %env) else (:cont %env))]
               (x-pred e then else)))
       (rule '(let ([?v ?e]) ?body)
             (let [body (x-assign (:var %env) body (:cont %env))]
               (x-assign v e body)))
       (rule '?value (-> (:cont %env)
                         (update :s (fn [s] (into [(sub (assign ~(:var %env) ?value))] s)))
                         (update :v (fnil conj #{}) (:var %env)))))]
  (defn x-assign [v exp cont]
    (first (x-assign* exp {:var v :cont cont}))))


(defn pred-block [{:keys [then else]} f]
  (let [then (assoc then :label (gennice 'then))
        else (assoc else :label (gennice 'else))]
    {:v (into (:v then) (:v else))
     :b (merge {(:label then) (dissoc then :b)
                (:label else) (dissoc else :b)}
               (:b then)
               (:b else))
     :s (f (:label then) (:label else))}))

(let [x-pred*
      (rule-list
       (rule '(if ?e ?then ?else)
             (let [then (x-pred then (:then %env) (:else %env))
                   else (x-pred else (:then %env) (:else %env))]
               (x-pred e then else)))
       (rule '(not ?e)
             (x-pred e (:else %env) (:then %env)))
       (rule true (:then %env))
       (rule false (:else %env))
       (rule '(let ([?v ?e]) ?body)
             (let [body (x-pred body (:then %env) (:else %env))]
               (x-assign v e body)))
       (rule '(? x list?)
             (pred-block %env #(sub [(if ?x (goto ~%1) (goto ~%2))])))
       (rule '?x
             ;; this may not be necessary since the lang is strictly type checked in theory.
             (x-pred (sub (eq? ?x true)) (:then %env) (:else %env))))]
  (defn x-pred [exp then else]
    (first (x-pred* exp {:then then :else else}))))

(def x-tail
  (rule-list
   (rule '(if ?e ?then ?else)
         (let [then (x-tail then)
               else (x-tail else)]
           (x-pred e then else)))
   (rule '(let ([?v ?e]) ?body)
         (let [body (x-tail body)]
           (x-assign v e body)))
   (rule '?x {:s [(sub (return ?x))]})))


(defn explicate-control [p]
  (let [p (x-tail p)
        blocks (reduce-kv (fn [blocks l b]
                            (assoc blocks l
                                   (sub (block ?l [~@(sort (:v b))]
                                               ~@(:s b)))))
                          {} (assoc (:b p) 'start (assoc p :label 'start)))]
    (sub (program [~@(:v p)] ~blocks))))

;; Select instructions: rewrite as data representing X86 assembly

(def unv-rax
  "This is an annoying hack because I don't mark symbols as (v x) in an earlier
  pass, so I end up with (v (reg rax)) in my return clause. This cleans that
  up."
  (on-subexpressions (rule '(v (reg rax)) '(reg rax))))

(def select-inst-cond*
  (rule-list!
   (rule '((? op #{< eq?}) ?a ?b)
         (let [v (:v %env)]
           (sub [(cmpq ?b ?a)
                 (set ?op (byte-reg al))
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

(defn make-tag [len type*]
  (bit-or 1
          (bit-shift-left len 1)
          (bit-shift-left
           (apply +
                  (map-indexed (fn [i t]
                                 (condp = t
                                   'Vector (bit-shift-left 1 i)
                                   0))
                               type*))
           7)))

(def select-instructions*
  ;; TODO: split to assign and tail versions.. See hints here
  ;; https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/lecture-Oct-6.html
  (directed (rule-list (rule '(program ?vars ?blocks)
                             (let [blocks (reduce-kv (fn [blocks l b]
                                                       (assoc blocks l (descend b)))
                                                     {} blocks)]
                               (sub (program ?vars ?blocks))))
                       (rule '(block ?label ?vars ??->instrs)
                             (sub (block ?label ?vars ~@(apply concat instrs))))
                       (rule '(assign ?->x (+ ?->a ?->b))
                             (cond (= x b) (sub [(addq ?a ?b)])
                                   (= x a) (sub [(addq ?b ?a)])
                                   :else (sub [(movq ?a ?x)
                                               (addq ?b ?x)])))
                       (rule '(assign ?->x (read))
                             (sub [(callq read-int)
                                   (movq (reg rax) ?x)]))
                       (rule '(assign ?->x (vector-ref ?->vec ?i))
                             (sub [(movq ?vec (reg r11))
                                   (movq (deref 8 ~(inc i) r11) ?x)]))

                       (rule '(assign ?->x (vector-set! ?->vec ?i ?->val))
                             (sub [(movq ?vec (reg r11))
                                   (movq ?val (deref 8 ~(inc i) r11))
                                   (movq (int 0) ?x)]))

                       (rule '(assign ?->x (allocate ?len (Vector ??type*)))
                             (let [tag (make-tag len type*)]
                               (sub [(movq (global-value free_ptr) (reg r11))
                                     (addq ~(* 8 (inc len)) (global-value free_ptr))
                                     (movq ?tag (deref 0 r11)) ;; why use deref here??
                                     (movq (reg r11) ?x)])))
                       (rule '(assign ?->x (collect ?->bytes))
                             (sub [(movq (reg r15) (reg rdi))
                                   (movq ?bytes (reg rsi))
                                   (callq collect)]))

                       (rule '(assign ?->x (- ?->a))
                             (if (= x a)
                               (sub [(negq ?x)])
                               (sub [(movq ?a ?x)
                                     (negq ?x)])))
                       (rule '(assign ?->x ((? op #{< eq?}) ?->a ?->b))
                             (select-inst-cond (sub (?op ?a ?b)) {:v x}))
                       (rule '(assign ?->x (not ?->a))
                             (select-inst-cond (sub (not ?a)) {:v x}))
                       (rule '(assign ?->x ?->a)
                             (if (= x a)
                               []
                               (sub [(movq ?a ?x)])))
                       (rule '(return ?->x)
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
                             (sub (v ?v)))
                       (rule '(void) '(int 0)))))

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
                                                (let [from (loop [b (blocks from)]
                                                             (if (symbol? b)
                                                               (recur (blocks b))
                                                               (:label b)))]
                                                  (if (and (blocks from) (blocks to))
                                                    (-> blocks
                                                        (update from (fn [b]
                                                                       (sub (~@(butlast b)
                                                                             ~@(drop 3 (blocks to))))))
                                                        (assoc to from))
                                                    blocks)))
                                              blocks linear-jumps)]
                               (sub (program ?var-locs [~@(remove symbol? (vals blocks))]))))
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
                                   ".globl main\n"
                                   blocks
                                   "main:\n"
                                   "    pushq %rbp\n"
                                   "    movq %rsp, %rbp\n"
                                   (apply str (fi save-regs))
                                   "    subq $" size ", %rsp\n"
                                   ;; TODO: inline start
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
                          (rule '(deref ?scale ?offset ?v)
                                (str scale "(" offset ")(%" (name v) ")"))
                          (rule '(deref ?offset ?v)
                                (str offset "(%" (name v) ")"))
                          (rule '(set ?op ?->y)
                                (let [flag ('{< l eq? e} op)]
                                  (str "set" flag " " y)))
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

(def ->shrink (comp #'shrink #'uniqify))
(def ->type (comp #'add-types #'->shrink))
(def ->simple (comp #'remove-complex-opera* #'->shrink))
(def ->flatten (comp #'explicate-control #'->simple))
(def ->select (comp #'select-instructions #'->flatten))
(def ->live (comp #'liveness #'->select))
(def ->alloc (comp #'allocate-registers #'->select))
(def ->jump (comp #'remove-jumps #'->alloc))
(def ->patch (comp #'patch-instructions #'->jump))
(def ->reg (comp #'save-registers #'->patch))
(def compile (comp println
                   #'stringify #'->reg))
(def ->compile (comp str/split-lines
                     #(str/replace (with-out-str (println %)) #"\t" "    ")
                     #'stringify #'->reg))
