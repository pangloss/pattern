(ns compiler-course.r1-dialects
  (:require [matches.nanopass.dialect :as d
             :refer [=> ==> ===> define-dialect derive-dialect]
             :rename {define-dialect def-dialect
                      derive-dialect def-derived}]))

;; I'm using this with 2 dimensions (book stage X pass progression) and it
;; doesn't work well. Forget about the previous book stage languages.
;;
;; NOTE: none of these languages reflect what I did. I am pulling them out of
;; the book after the fact. Perhaps will update my passes to match?

(define-dialect R-Var
  (terminals [i int?]
             [v symbol?])
  (Exp [e]
       ?i ?v
       (read)
       (- ?e)
       (+ ?e0 ?e1)
       (let ([?v ?e] ?e:body))))


(def-derived R-If R-Var
  (terminals + [b boolean?]
             + [cmp `cmp?])
  (Exp [e]
       + ?b
       + (- ?e0 ?e1)
       + (and ?e0 ?e1)
       + (or ?e0 ?e1)
       + (not ?e)
       + (?cmp ?e0 ?e1)
       + (if ?e ?e:then ?e:else)))



(def-dialect R-AbsVar
  (terminals [i int?]
             [v symbol?])
  (Exp [e]
       (Int ?i)
       (Var ?v)
       (Prim read ())
       (Prim - (?e))
       (Prim + (?e0 ?e1))
       (Let ?v ?e0 ?e:body))
  (Program [p]
           (Program () ?e)))

(def-derived C-AbsVar R-AbsVar
  (Atm [atm]
       (Int ?i)
       (Var ?v))
  (Exp [e]
       - (Int ?a)
       - (Var ?v)
       + ?atm)
  (Stmt [stmt]
        (Assign (Var ?v) ?e))
  (Tail [tail]
        (Return ?e)
        (Seq ?stmt ?tail))
  - Program
  (Program [p]
           (CProgram ?info (?:* [?label ?tail]))))

(def cmp2? #{'eq? '<})

(def-derived C-If C-AbsVar
  (terminals + [b boolean?]
             + [cmp `cmp2?])
  (Atm [atm]
       + (Bool ?b))
  (Exp [exp]
       + (Prim not (?atm))
       + (Prim cmp (?atm ?atm)))
  (Tail [tail]
        + (Goto ?label)
        + (IfStmt (Prim ?cmp (?atm ?atm)) (Goto ?label) (Goto ?label))))




;; I didn't bother with X86-Var

(def-dialect X86-If
  (terminals [label symbol?]
             [i int?])
  (BReg [bytereg] ah al bh bl ch cl dh dl)
  (Arg [arg]
       (Imm ?i) (Reg ?reg) (Deref ?reg ?i) (ByteReg ?bytereg))
  (CC [cc] e l le g ge)
  (Instruction [instr]
               (Instr addq (?arg0 ?arg1))
               (Instr subq (?arg0 ?arg1))
               (Instr movq (?arg0 ?arg1))
               (Instr negq (?arg))
               (Callq ?label ?i)
               (Pushq ?arg)
               (Popq ?arg)
               (Jmp ?label)
               (Instr xorq (?arg0 ?arg1))
               (Instr cmpq (?arg0 ?arg1))
               (Instr set (?cc ?arg))
               (Instr movzbq (?arg0 ?arg1))
               (JmpIf ?cc ?label))
  (Block [block]
         (Block ?info (??instr)))
  (Top [top] (X86Program ?info ((?:* [?label ?block])))))
