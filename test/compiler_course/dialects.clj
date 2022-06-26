(ns compiler-course.dialects
  (:require [pattern.nanopass.dialect :as d
             :refer [=> ==> ===> def-dialect def-derived show-dialect
                     validate valid? show-parse]]
            [pattern.types :refer [ok]]
            [pattern :refer [matcher]]))

(def cmp? #{'eq? '< '<= '> '>=})

(def r1-keyword? (into cmp? '[define let if and or not void read + -
                              vector vector-length vector-ref vector-set]))

(def-dialect R1
  (terminals [i int?]
             [v symbol?]
             [b boolean?]
             [cmp `cmp?])
  (Type [type :enforce]
        (?:letrec [simple   (| Integer Boolean Void)
                   compound (Vector (?:* $type))
                   function ((?:* $type) -> $type)
                   closure  (Vector #_closure-fn       ((| (Vector ??_) Void)
                                                        (?:* $type) -> $type)
                                    #_closed-over-vars (?:* $type))
                   type     (| $simple $compound $function $closure)]
          $type))
  (ArgDef [argdef] [?v ?type])
  (Exp [e]
       ?i ?v ?b
       (read)
       (- ?e) (+ ?e0 ?e1) (- ?e0 ?e1)
       (and ?e0 ?e1) (or ?e0 ?e1) (not ?e)
       (?cmp ?e0 ?e1)
       (let ([?v ?e]) ?e:body)
       (if ?e ?e:then ?e:else)
       (lambda (??argdef*) ?type ?e)
       (vector ??e*) (vector-length ?e)
       (vector-ref ?e ?i) (vector-set! ?e0 ?i ?e1)
       (void)
       ;; FIXME: this list should not unify with a vector... but it does if I don't add the (? _ seq?) rule.
       (& (?e:f ??e:args) (? _ seq?)))
  (Define [define]
    (define (?v:name ??argdef*) ?type ?e))
  (Program [p]
           ;; Programs have mulitple top-level forms, so just contain them in a vector
           ?e
           [??define* ?e])
  (entry Program))

(def-derived R1Fun R1
  - Program
  (Program [p] (program ??define*)))

(def-derived Shrunk R1Fun
  (terminals - [cmp `cmp?])
  (Exp [e]
       - (- ?e0 ?e1)
       - (?cmp ?e0 ?e1)
       + (< ?e0 ?e1)
       + (eq? ?e0 ?e1)
       - (and ?e0 ?e1)
       - (or ?e0 ?e1)
       ;; put this in here early because without call, fns are inconvenient.
       + (call ?e:f ??e:args)
       - (& (?e:f ??e:args) (? _ seq?))))

(def-derived Exposed Shrunk
  (Exp [e]
       + (funref ?v)))

(def-derived Closures Exposed
  - Type
  (Type [type :enforce]
        (?:letrec [simple   (| Integer Boolean Void Closure (delay-type ??_))
                   compound (Vector (?:* $type))
                   function ((?:* $type) -> $type)
                   ;; closure is a vector whose first arg contains itself recursively (or Void)
                   closure  (Vector #_closure-fn       ((| (Vector ??_) Void)
                                                        (?:* $type) -> $type)
                                    #_closed-over-vars (?:* $type))
                   type     (| $simple $compound $function $closure)]
                  $type))
  (Exp [e]
       ;; lambdas become top-level define plus a vector of free variable values where the lambda was.
       ;; calls to the return lambda become calls to the first member of the vector which is the funref
       - (lambda (??argdef*) ?type ?e)))

(def-derived Typed Closures ;; dead end dialect :)
  (Exp [e {:r1/type ?type}]))

(def-derived Alloc Closures
  (terminals + [name symbol?])
  (Exp [e]
       - (vector ??e*)
       + (collect ?i)
       + (allocate ?i ?type)
       + (global-value ?name)))

(def-derived AllocTyped Alloc ;; dead end dialect :)
  (Exp [e {:r1/type ?type}]))

;; FIXME: for some reason setting ?atm to be enforced causes downstream tests to fail. Not sure why...
;; - It doesn't change the output of the simplified pass
;; - the failing data seems valid, but the data doesn't validate.
;; - perhaps this is a bug within the checker?
(def-derived Simplified Alloc
  (Atom [atm #_:enforce]
        (read)
        ?i ?v ?b)
  - Exp
  (NotExp [ne]
          ?e
          (not ?ne))
  (Exp [e]
       ?atm
       (- ?atm)
       (+ ?atm0 ?atm1)
       (< ?atm0 ?atm1)
       (eq? ?atm0 ?atm1)
       (not ?atm)
       (let ([?v ?e]) ?e:body)
       (if ?ne ?e:then ?e:else)
       (vector-ref ?e ?i) (vector-set! ?e0 ?i ?e1)
       (void)
       (funref ?v)
       (call ?e:f ??e:args)
       (collect ?i)
       (allocate ?i ?type)
       (global-value ?name)))

;; The book's C... language:
(def-derived Explicit Simplified
  (terminals + [lbl symbol?])
  - Exp
  - NotExp
  (Pred [pred :enforce]
        ?b
        ?v
        (not ?pred)
        (< ?atm0 ?atm1)
        (eq? ?atm0 ?atm1)
        (vector-ref ?v ?i)
        (if ?pred (goto ?lbl:then) (goto ?lbl:else)))
  (Atom [atm :enforce]
        + (void)
        + (global-value ?name))
  (Exp [e]
       ?atm
       ?pred
       (+ ?atm0 ?atm1) (- ?atm)
       (vector-ref ?v ?i)
       (vector-set! ?v ?i ?atm)
       (collect ?i)
       (allocate ?i ?type)
       ;; calls become (let ([x (funref f)]) (call x ..)) ... or tailcall
       (funref ?lbl) (call ?v ??atm*))
  (Stmt [stmt]
        (assign ?v ?e))
  (Tail [tail]
        (if ?pred (goto ?lbl:then) (goto ?lbl:else))
        (tailcall ?v ??atm*)
        (return ?e))
  (Block [block]
         (block ?lbl ??stmt* ?tail))
  (ArgDef [argdef] [?v ?type])
  - Define
  (DefInfo [d]
    [?lbl [??argdef*] ?type])
  (Define [define]
    (define ?d [??v*]
      ;; the book specifies an undefined ?info here, too...
      (?:+map ?lbl* ?block*))))


(def-derived Uncovered Explicit
  - Define
  (Define [define]
    (define ?d
      (?:*map ?v ?type)
      (?:+map ?lbl* ?block*))))

(def-derived Uncovered+ Uncovered
  ;; During select-instructions (assign (reg rax) ...) can happen.
  (Loc [x :enforce]
       ?v
       (reg rax))
  (Stmt [stmt]
        - (assign ?v ?e)
        + (assign ?x ?e)))

(def jmp-cond #{true '< 'eq?})

(def-dialect Selected
  (terminals [lbl symbol?]
             [v symbol?]
             [i int?]
             [jc `jmp-cond])
  (Type [type :enforce]
        (?:letrec [simple   (| Integer Boolean Void Closure (delay-type ??_))
                   compound (Vector (?:* $type))
                   function ((?:* $type) -> $type)
                   ;; closure is a vector whose first arg contains itself recursively (or Void)
                   closure  (Vector #_closure-fn       ((| (Vector ??_) Void)
                                                        (?:* $type) -> $type)
                                    #_closed-over-vars (?:* $type))
                   type     (| $simple $compound $function $closure)]
                  $type))
  (ByteReg [bytereg :enforce] (byte-reg (| ah al bh bl ch cl dh dl)))
  (Reg [reg]
       (reg (| rdi rsi rdx rcx r8 r9)) ;; fn arg regs
       (reg (| rax r11 r15 rsi rdi)))  ;; used in various places
  (Arg [arg]
       ?reg
       (int ?i)
       (deref ?i:offset ?reg)
       (deref ?i:scale ?i:offset ?reg)
       (v ?v)
       (global-value ?lbl))
  ;; this could get fancy and encode some of the restrictions
  (Stmt [stmt]
        (callq ?lbl)
        (cmpq ?arg0 ?arg1)
        (movq ?arg0 ?arg1)
        (addq ?arg0 ?arg1)     ; (+ 1 2)
        (negq ?arg)            ; (- 1)
        (xorgq (int 1) ?arg)   ; (not 1)
        (set ?jc ?bytereg)     ; get cmp flag 1
        (movzbq ?bytereg ?arg) ; get cmp flag 2
        (jump ?jc ?lbl)
        (indirect-callq ?arg)  ; I originally had an extra (int ?i) here and on tailjmp. Why?
        (leaq (funref ?v) ?arg))
  ;; there is specific valid sequencing like cmp -> jump -> jump, but I'm not
  ;; sure how or if I can encode that here...
  ;; TODO: attach additional validation rules to forms? Some could have rules
  ;; like above attached but they don't fit at the expression level.
  (Tail [tail]
        (jump ?jc ?lbl)
        (tailjmp ?arg)
        (retq))
  (Block [block]
         (block ?lbl ??stmt* ?tail))
  ;; FIXME: think about if this changes?
  (Define [define]
    (define ?v (?:*map ?v* ?type*) (?:*map ?lbl* ?block*)))
  (Program [program]
           (program ??define*))
  (entry Program))

(def-derived RegAllocated Selected
  (Caller [caller :enforce] (reg (| rax rcx rdx rsi rdi r8 r9 r10 r11)))
  (Callee [callee :enforce] (reg (| rsp rbp rbx r12 r13 r14 r15)))
  - Reg
  (Reg [reg] ?caller ?callee)
  (Loc [loc]
       ?reg
       (stack ?i)
       (heap ?i))
  (Arg [arg]
       - ?reg
       + ?loc)
  - Define
  (Define [define]
    (define ?v
      (?:*map ?v*1 ?type)
      (?:*map ?v*2 ?loc*)
      [??block*])))

(def-derived RemoveUnallocated RegAllocated
  (Arg [arg]
       - (v ?v)))

(def-derived Patched RemoveUnallocated
  (Stmt [stmt]
        - (movq ?arg0 ?arg1)
        + (movq ?arg0 (& ?arg1 (? arg1 not= ?arg0)))
        - (addq ?arg0 ?arg1)
        + (addq (& ?arg0 (? arg0 not= (int 0))) ?arg1)))


(def-derived Patched+ Patched
  (SaveReg [savereg]
           (movq ?callee (stack* ?i)))
  - Define
  (Define [define]
    (define ?v
      (?:*map ?v*1 ?type)
      (?:*map ?v*2 ?loc*)
      [??savereg*]
      [??block*])))
