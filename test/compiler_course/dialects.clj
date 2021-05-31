(ns compiler-course.dialects
  (:require [matches.nanopass.dialect :as d
             :refer [=> ==> ===> define-dialect derive-dialect unparse-dialect
                     validate valid?]
             :rename {define-dialect def-dialect
                      derive-dialect def-derived}]))

(def cmp? #{'eq? '< '<= '> '>=})

(def-dialect R1
  (terminals [i int?]
             [v symbol?]
             [b boolean?]
             [cmp `cmp?])
  (Exp [e]
       ?i ?v ?b
       (read)
       (- ?e)
       (+ ?e0 ?e1)
       (let ([?v ?e]) ?e:body)
       (- ?e0 ?e1)
       (and ?e0 ?e1)
       (or ?e0 ?e1)
       (not ?e)
       (?cmp ?e0 ?e1)
       (if ?e ?e:then ?e:else)))

(def-derived Shrunk R1
  (terminals - [cmp `cmp?])
  (Exp [e]
       - (- ?e0 ?e1)
       - (?cmp ?e0 ?e1)
       + (< ?e0 ?e1)
       + (eq? ?e0 ?e1)
       - (and ?e0 ?e1)
       - (or ?e0 ?e1)))


(def-derived Simplified Shrunk
  (Atom [atm]
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
       (if ?ne ?e:then ?e:else)))

(def-derived Explicit Simplified
  (terminals + [lbl symbol?])
  - Exp
  - NotExp
  (Pred [pred]
        ?b
        (not ?pred)
        (< ?atm0 ?atm1)
        (eq? ?atm0 ?atm1)
        (if ?pred (goto ?lbl:then) (goto ?lbl:else)))
  (Exp [e]
       ?atm
       ?pred
       (+ ?atm0 ?atm1)
       (- ?atm))
  (Stmt [stmt]
        ?e
        (assign ?v ?e))
  (Tail [tail]
        (if ?pred (goto ?lbl:then) (goto ?lbl:else))
        (return ?e))
  (Block [block]
         (block ?lbl [??v*] ??stmt* ?tail))
  (Program [program]
           (program [??v*] (?:+map ?lbl* ?block*))))

(def jmp-cond #{true '< 'eq?})

(def-dialect Selected
  (terminals [lbl symbol?]
             [v symbol?]
             [i int?]
             [jc `jmp-cond])
  (ByteReg [bytereg] (byte-reg (| ah al bh bl ch cl dh dl)))
  (Arg [arg]
       (reg rax)
       (int ?i)
       (v ?v))
  ;; this could get fancy and encode some of the restrictions
  (Stmt [stmt]
        (callq read-int)
        (cmpq ?arg0 ?arg1)
        (movq ?arg0 ?arg1)
        (addq ?arg0 ?arg1)     ; (+ 1 2)
        (negq ?arg)            ; (- 1)
        (xorgq (int 1) ?arg)   ; (not 1)
        (set ?jc ?bytereg)     ; get cmp flag 1
        (movzbq ?bytereg ?arg) ; get cmp flag 2
        (jump ?jc ?lbl))
  ;; there is specific valid sequencing like cmp -> jump -> jump, but I'm not
  ;; sure how or if I can encode that here...
  (Tail [tail]
        (jump ?jc ?lbl)
        (retq))
  (Block [block]
         (block ?lbl [??v*] ??stmt* ?tail))
  (Program [program]
           (program [??v*] (?:+map ?lbl* ?block*))))



(def-derived Future Selected
  (Arg [arg]
       (stack ?i))
  (CC [cc] e l le g ge) ;; really just e and l though?
  (Instruction [instr]
               (pushq ?arg)
               (popq ?arg)))
