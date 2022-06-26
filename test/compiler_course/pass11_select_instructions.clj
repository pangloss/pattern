(ns compiler-course.pass11-select-instructions
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


;; Select instructions: rewrite as data representing X86 assembly

(def unv-rax
  "This is an annoying hack because I don't mark symbols as (v x) in an earlier
  pass, so I end up with (v (reg rax)) in my return clause. This cleans that
  up."
  (on-subexpressions (rule '(v (reg rax)) '(reg rax))))

(def select-inst-cond*
  (dialects
   (=> Uncovered Selected)
   (rule-list!
    (rule '((? op #{< eq?}) ?e:a ?e:b)
          (let [v (:v %env)]
            (sub [(cmpq ?b ?a)
                  (set ?op (byte-reg al))
                  (movzbq (byte-reg al) ?v)])))
    (rule '(not ?->e:a)
          (let [v (:v %env)]
            (if (= v a)
              (sub [(xorq (int 1) ?v)])
              (sub [(movq ?a ?v)
                    (xorgq (int 1) ?v)]))))
    (rule '(vector-ref ?vec ?i)
          (let [v (:v %env)]
            (sub [(movq (v ?vec) (reg r11))
                  (movq (deref 8 ~(inc i) (reg r11)) ?v)])))
    (rule '(v ?x)
          (sub [(movq (v ?x) ~(:v %env))])))))

(defn select-inst-cond
  {:=>/from 'Uncovered :=>/to 'Selected}
  [x env]
  (first (select-inst-cond* x env)))

(defn make-tag [len type*]
  (bit-or 1
          (bit-shift-left len 1)
          (bit-shift-left
           (reduce bit-or
                   (map-indexed (fn [i t]
                                  (condp = t
                                    'Vector (bit-shift-left 1 i)
                                    0))
                                type*))
           7)))

(def select-instructions*
  ;; TODO: split to assign and tail versions.. See hints here
  ;; https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/lecture-Oct-6.html
  (letfn [(fn-args [arg*]
            (map (fn [arg reg]
                   (sub (movq ?arg (reg ?reg))))
                 arg*
                 '[rdi rsi rdx rcx r8 r9]))
          (extract-fn-args [[_ label vars & instrs] args]
            (let [prefix (map (fn [reg arg]
                                (sub (movq (reg ?reg) (v ?arg))))
                              '[rdi rsi rdx rcx r8 r9]
                              args)]
              (sub (block ?label ??prefix ??instrs))))]
    (dialects
     (=> Uncovered+ Selected)
     (directed (rule-list (rule '(program ??->define*))
                          (rule '(define [?v [[?v* ?type*] ...] ?type] ?vars ?blocks)
                                (let [blocks (reduce-kv (fn [blocks l b]
                                                          (assoc blocks l (descend b)))
                                                        {} blocks)
                                      start (symbol (str v "-start"))
                                      blocks (update blocks start extract-fn-args v*)
                                      vars (into (or vars {}) (map vector v* type*))]
                                  (sub (define ?v ?vars ?blocks))))
                          (rule '(block ?label ??->instrs)
                                (sub (block ?label ~@(apply concat instrs))))
                          (rule '(assign ?->x (+ ?->atm:a ?->atm:b))
                                (cond (= x b) (sub [(addq ?a ?b)])
                                      (= x a) (sub [(addq ?b ?a)])
                                      :else (sub [(movq ?a ?x)
                                                  (addq ?b ?x)])))
                          (rule '(assign ?->x (read))
                                (sub [(callq read-int)
                                      (movq (reg rax) ?x)]))
                          (rule '(assign ?->x (vector-ref ?->v:vec ?i))
                                (sub [(movq ?vec (reg r11))
                                      (movq (deref 8 ~(inc i) (reg r11)) ?x)]))

                          (rule '(assign ?->x (vector-set! ?->v:vec ?i ?->atm:val))
                                (sub [(movq ?vec (reg r11))
                                      (movq ?val (deref 8 ~(inc i) (reg r11)))
                                      (movq (int 0) ?x)]))

                          (rule '(assign ?->x (allocate ?i:len (Vector ??type*)))
                                (let [tag (make-tag len type*)
                                      free (sub (v ~(gennice 'free)))]
                                  (sub [(movq (global-value free_ptr) ?free)
                                        (addq (int ~(* 8 (inc len))) (global-value free_ptr))
                                        (movq ?free (reg rax))
                                        (movq (int ?tag) (deref 0 (reg rax))) ;; why use deref here??
                                        (movq ?free ?x)])))
                          (rule '(assign ?->x (collect ?->i:bytes))
                                ;; TODO: can I deal with the existence of these
                                ;; registers in the allocator and not cause
                                ;; clobbering without just removing them from the
                                ;; list of avail regs?  OOOH yes, these method
                                ;; calls need to interfere with the callee-save
                                ;; registers.
                                (sub [(movq (reg r15) (reg rdi))
                                      (movq ?bytes (reg rsi))
                                      (callq collect)]))

                          (rule '(assign ?->x (funref ?lbl))
                                (sub [(leaq (funref ?lbl) ?x)]))
                          (rule '(assign ?->x (call ?v:fr ??->atm:args))
                                (sub [~@(fn-args args)
                                      (indirect-callq (v ?fr))
                                      (movq (reg rax) ?x)]))

                          (rule '(assign ?->x (- ?->e:a))
                                (if (= x a)
                                  (sub [(negq ?x)])
                                  (sub [(movq ?a ?x)
                                        (negq ?x)])))
                          (rule '(assign ?->x ((? op #{< eq?}) ?->atm:a ?->atm:b))
                                (select-inst-cond (sub (?op ?a ?b)) {:v x}))
                          (rule '(assign ?->x (not ?->pred:a))
                                (select-inst-cond (sub (not ?a)) {:v x}))
                          (rule '(assign ?->x ?->e:a)
                                (if (= x a)
                                  []
                                  (sub [(movq ?a ?x)])))
                          (rule '(return ?->e:x)
                                (concat (unv-rax
                                         ;; Will produce a vector of statements:
                                         (descend (sub (assign (reg rax) ?x))))
                                        ['(retq)]))

                          (rule '(tailcall ?v:fr ??->atm:args)
                                (sub [~@(fn-args args)
                                      (tailjmp (v ?fr))]))


                          (rule '(if ((? cmp #{< eq?}) ?->atm:a ?->atm:b) (goto ?lbl:then) (goto ?lbl:else))
                                (sub [(cmpq ?b ?a)
                                      (jump ?cmp ?then)
                                      (jump true ?else)]))

                          (rule '(if ?->pred:exp (goto ?lbl:then) (goto ?lbl:else))
                                (concat
                                 (select-inst-cond exp {:v (sub (v ~(gennice 'if)))})
                                 (sub [(cmpq (int 1) (v tmp))
                                       (jump eq? ?then)
                                       (jump true ?else)])))

                          (rule true '(int 1))
                          (rule false '(int 0))
                          (rule '?i
                                (sub (int ?i)))
                          (rule '?v
                                (sub (v ?v)))
                          (rule '(void) '(int 0)))))))

(defn select-instructions
  {:=>/from 'Uncovered :=>/to 'Selected}
  [x]
  (select-instructions* x))
