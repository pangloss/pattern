(ns compiler-course.dialects
  (:require [matches.nanopass.dialect :as d
             :refer [=> ==> ===> define-dialect derive-dialect unparse-dialect
                     validate valid?]
             :rename {define-dialect def-dialect
                      derive-dialect def-derived}]))

(def cmp? #{'eq? '< '<= '> '>=})

(define-dialect R1
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
        ?i ?v ?b
        (read))
  - Exp
  (Exp [e]
       ?atm
       (- ?atm)
       (+ ?atm0 ?atm1)
       (< ?atm0 ?atm1)
       (eq? ?atm0 ?atm1)
       (not ?atm)
       (let ([?v ?e]) ?e:body)
       (if ?ne ?e:then ?e:else))
  (NotExp [ne]
          ?e
          (not ?ne)))

(def-derived Explicit Simplified
  (terminals + [lbl symbol?])
  (Atom [atm]
        - ?i
        - ?v
        + (int ?i)
        + (v ?v))
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
         (block ?label [??v*] ??stmt* ?tail))
  (Program [program]
           (program [??v*] (?:+map ?lbl* ?block*))))
