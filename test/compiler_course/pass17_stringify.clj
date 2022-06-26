(ns compiler-course.pass17-stringify
  (:require
   [pattern :refer [=> descend dialects directed matcher rule rule-list sub]]))


;; Stringify: Turn the data representing X86 assembly into actual assembly

(defn stack-var-max [var-locs]
  (->> (vals var-locs)
       (filter #(= 'stack (first %)))
       (map second)
       (apply max 0)))

(defn stack-size [offset var-locs]
  (let [stack-vars (+ offset (stack-var-max var-locs))]
    (* 16 (max 1 (int (Math/ceil (/ stack-vars 2)))))))

(def stringify*
  (dialects
   (=> Patched+ nil)
   (letfn [(fi [i*] (map (fn [x]
                           (let [x (if (sequential? x) x [x])]
                             (sub ["    " ??x])))
                         i*))
           (init-gc [root-stack-size heap-size root-spills]
             (sub [(movq (int ?root-stack-size) (reg rdi))
                   ;; TODO: how to distinguish "root stack" size and heap size?
                   ;; heap must include all of the memory pointed to (or default start size?)
                   ;; root-stack may also be a fixed size?
                   ;; root-spills is the max number currently used??
                   (movq (int ?heap-size) (reg rsi))
                   (callq initialize)
                   (movq (global-value rootstack_begin) (reg r15))
                   ~@(map (fn [i]
                            (sub (movq (int 0) (deref ?i (reg r15)))))
                          (range root-stack-size))
                   (addq (int ?root-spills) (reg r15))]))]

     (directed (rule-list (rule '(program ??->define*)
                                (apply concat define*))
                          (rule '(define ?d ?vars ?var-locs [??->save-regs] ?block*)
                                (let [offset (count save-regs)
                                      block* (apply concat (map #(first (descend % {:stack-offset offset}))
                                                                block*))
                                      size (stack-size offset var-locs)
                                      heap-size (->> (vals var-locs)
                                                     (keep (matcher '(heap ?h)))
                                                     (map first)
                                                     (apply max -1)
                                                     inc)]
                                  (sub
                                   [[".globl main"]
                                    ~@block*
                                    ["main:"]
                                    ["    pushq %rbp"]
                                    ["    movq %rsp, %rbp"]
                                    ~@(fi save-regs)
                                    [~(str "    subq $" size ", %rsp")]
                                    ~@(fi (map descend (init-gc heap-size
                                                                heap-size
                                                                heap-size)))
                                    ;; TODO: inline start. This could be treated
                                    ;; as a nearly empty regular block, existing
                                    ;; from the beginning, then with instructions
                                    ;; added to it at the end?
                                    ["    jmp start"]
                                    ["conclusion:"]
                                    [~(str "    addq $" size ", %rsp")]
                                    ["    popq %rbp"]
                                    ["    retq"]])))

                          (rule '(block ?lbl ??->all*)
                                (list* [(str (name lbl) ":")]
                                       (fi all*)))

                          (rule '(funref ?lbl)                  (str lbl "(%rip)"))
                          (rule '(byte-reg ?r)                  (str "%" r))
                          (rule '(deref ?i:offset (reg ?v))           (str offset "(%" (name v) ")"))
                          (rule '(deref ?i:scale ?i:offset (reg ?v))  (str scale "(" offset ")(%" (name v) ")"))
                          (rule '(global-value ?lbl)            (str (name lbl) "(%rip)"))
                          (rule '(int ?i)                       (str "$" i))
                          (rule '(reg ?r)                       (str "%" r))
                          (rule '(stack* ?i)                    (str (* -8 (inc i)) "(%rbp)"))
                          (rule '(stack ?i)
                                (str (* -8 (inc (+ (:stack-offset %env) i)))
                                     "(%rbp)"))
                          (rule '(heap ?i)                      (str (* 8 (inc i)) "(%r15)"))

                          (rule '(set ?jc ?->bytereg)
                                (let [flag ('{< l eq? e} jc)]
                                  (list "set" (str flag) " " bytereg)))
                          (rule '(callq ?lbl)             (list "callq " (name lbl)))
                          (rule '(jump < ?lbl)            (list "jl " (name lbl)))
                          (rule '(jump eq? ?lbl)          (list "je " (name lbl)))
                          (rule '(jump true ?lbl)         (list "jmp " (name lbl)))
                          (rule '(indirect-callq ?->arg)  (list "callq *" arg))
                          (rule '(tailjmp ?lbl)           (list "jmp *" lbl))
                          (rule '(retq)                   ["jmp conclusion"])
                          (rule '(?x ?->a)                (list (name x) " " a))
                          (rule '(?x ?->a ?->b)           (list (name x) " " a ", " b)))))))

(defn stringify
  {:=>/from 'Patched+}
  [p]
  (stringify* p))

;; Turn the list of strings into one big string

(defn combine-strings [p]
  (apply str (map #(apply str (conj % "\n")) p)))
