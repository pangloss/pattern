(ns scheme-to-c.dialects
  (:require [pattern.nanopass.dialect :refer [def-dialect def-derived show-dialect]]))

(defmacro make-terminal [pred]
  ;; assume a ? at the end...
  (let [name (apply str (butlast (name pred)))
        tname (symbol (str name "-terminal"))
        value 'value]
    `(do
       (defrecord ~tname [~value])
       (defn ~pred [x#] (instance? ~tname x#)))))

(make-terminal datum?)
(make-terminal variable?)
(make-terminal primitive-info?)
(make-terminal immediate?)
(make-terminal label?)

(make-terminal primitive-info?)
(make-terminal value-primitive-info?)
(make-terminal predicate-primitive-info?)
(make-terminal effect-primitive-info?)

(make-terminal exact-integer?)
(make-terminal relational-operator?)
(make-terminal binary-operator?)

(def-dialect RawSrc
  (terminals [id `symbol?]
             [f `fn?]
             [d `datum?]))

(def-dialect Lsrc
  (terminals [d `datum?]
             [x `variable?]
             [pr `primitive-info?])
  (Expr [e]
        ?x
        (quote ?d)
        (if ?e0 ?e1 ?e2)
        (begin ??e* ?e)
        (set! ?x ?e)
        (lambda (??x*) ?e)
        (let ((?:* [?x* ?e*])) ?e)
        (letrec ((?:* [?x* ?e*])) ?e)
        (?callable ??e*))
  (Callable [callable]
            ?e
            ?pr))

(def-derived Ldatum Lsrc
  (terminals
   - [d `datum?]
   + [i `immediate?])
  (Expr [e]
        - (quote ?d)
        + (quote ?i)))

(def-derived Lletrec Ldatum
  (Expr [e]
        - (lambda (??x*) ?e)
        - (letrec ((?:* [?x* ?e*])) ?e)
        + ?f
        + (letrec ((?:* [?x* ?f*])) ?e))
  (Lambda [f]
          + (lambda (??x*) ?e)))

(def-derived Lno-assign Lletrec
  (Expr [e]
        - (set! ?x ?e)))

(def-derived Lsanitized Lno-assign
  (Expr [e]
        - ?f))

(def-derived Lfree Lsanitized
  (Lambda [f]
          - (lambda (??x*) ?e)
          + (lambda (??x*) ?frbody))
  (FreeBody [frbody]
            + (free (??x*) ?e)))

(def-derived Lclosure Lfree
  (terminals
   + [l `label?])
  (Expr [e]
        - (letrec ((?:* [?x* ?f*])) ?e)
        + ?l
        + (letrec ((?:* [?l* ?f*])) ?clbody))
  (ClosureBody [clbody]
               + (closures ([x* l* ??x**] ...) ?e))
  (Lambda [f]
          - (lambda (??x*) ?frbody)
          + (lambda (??x*) bfrbody))
  - FreeBody
  (BindFreeBody [bfrbody]
                + (bind-free (?x ??x*) ?e)))

(def-derived Lproc Lclosure
  (Expr [e]
        - (letrec ((?:* [?l* ?f*])) ?clbody)
        + (letrec ((?:* [?l* ?f*])) ?e))
  - ClosureBody
  (Lambda [f]
          - (lambda (??x*) bfrbody)
          + (lambda (??x*) ?e))
  - BindFreeBody)

(def-derived Llifted Lproc
  (entry Program)
  (Program [prog]
           + (letrec ((?:* [?l* ?f*])) ?e))
  (Expr [e]
        - (letrec ((?:* [?l* ?f*])) ?e)))

(def-derived Lnormalized Llifted
  (terminals
   - [pr `primitive-info?]
   + [value-pr `value-primitive-info?]
   + [pred-pr `predicate-primitive-info?]
   + [effect-pr `effect-primitive-info?])
  (Program [prog]
           - (letrec ((?:* [?l* ?f*])) ?e)
           + (letrec ((?:* [?l* ?f*])) ?v))
  (Lambda [f]
          - (lambda (??x*) ?e)
          + (lambda (??x*) ?v))
  - Expr
  - Callable
  (Value [v]
         + ?l
         + ?x
         + (quote ?i)
         + (if ?pr0 ?v1 ?v2)
         + (begin ??ef* ?v)
         + (let ((?:* [?x* ?v*])) ?v)
         + (?vcallable ??v*))
  (ValueCallable [vcallable]
                 + ?v
                 + ?value-pr)
  (Pred [pr]
        + (true)
        + (false)
        + (if ?pr0 ?pr1 ?pr2)
        + (begin ??ef* ?pr)
        + (let ((?:* [?x* ?v*])) ?pr)
        + (?pred-pr ??v*))
  (Effect [ef]
          + (nop)
          + (if ?pr0 ?ef1 ?ef2)
          + (begin ??ef* ?ef)
          + (let ((?:* [?x* ?v*])) ?ef)
          + (ecallable ??v*))
  (EffectCallable [ecallable]
                  + ?v
                  + ?effect-pr))

(def-derived Lrep Lnormalized
  (terminals
   - [i `immediate?]
   - [value-pr `value-primitive-info?]
   - [pred-pr `predicate-primitive-info?]
   - [effect-pr `effect-primitive-info?]
   + [int `exact-integer?]
   + [relop `relational-operator?]
   + [binop `binary-operator?])
  (Triv [tr]
        + ?x
        + ?int
        + ?l)
  (Value [v]
         - ?l
         - ?x
         - (quote ?i)
         - (?vcallable ??v*)
         + ?tr
         + (alloc ?v)
         + (mref ?v0 ?v1)
         + (?binop ?v0 ?v1)
         + (call ?v ??v*))
  - ValueCallable
  (Pred [pr]
        - (?pred-pr ??v*)
        + (?relop ?v0 ?v1))
  (Effect [ef]
          - (ecallable ??v*)
          + (mset! ?v0 ?v1 ?v2)
          + (call ?v ??v*))
  - EffectCallable)

(def-derived Llocals Lrep
  (Program [prog]
           - (letrec ((?:* [?l* ?f*])) ?v)
           + (letrec ((?:* [?l* ?f*])) ?b))
  (Lambda [f]
          - (lambda (??x*) ?v)
          + (lambda (??x*) ?b))
  (Body [b]
        + (locals (??x*) ?v)))

(def-derived Lno-let Llocals
  (Value [v]
         - (let ((?:* [?x* ?v*])) ?v))
  (Pred [pr]
        - (let ((?:* [?x* ?v*])) ?pr))
  (Effect [ef]
          - (let ((?:* [?x* ?v*])) ?ef)
          + (set! ?x ?v)))

(def-derived Lsimple-opnd Lno-let
  (Pred [pr]
        - (?relop ?v0 ?v1)
        + (?relop ?tr0 ?tr1))
  (Value [v]
         - (?binop ?v0 ?v1)
         - (call ?v ??v*)
         - (mref ?v0 ?v1)
         - (alloc ?v)
         + (?binop ?tr0 ?tr1)
         + (call ?tr ??tr*)
         + (mref ?tr0 ?tr1)
         + (alloc ?tr))
  (Effect [ef]
          - (call ?v ??v*)
          - (mset! ?v0 ?v1 ?v2)
          + (call ?tr ??tr*)
          + (mset! ?tr0 ?tr1 ?tr2)))

(def-derived Lflat-set! Lsimple-opnd
  (Effect [ef]
          - (set! ?x ?v)
          + (set! ?x ?rhs))
  (Rhs [rhs]
       + ?tr
       + (alloc ?tr)
       + (mref ?tr0 ?tr1)
       + (?binop ?tr0 ?tr1)
       + (call ?tr ??tr*))
  (Body [b]
        - (locals (??x*) ?v)
        + (locals (??x*) ?t))
  (Tail [t]
        + ?tr
        + (?binop ?tr0 ?tr1)
        + (alloc ?tr)
        + (mref ?tr0 ?tr1)
        + (call ?tr ??tr*)
        + (if ?pr0 ?t1 ?t2)
        + (begin ??ef* ?t))
  - Value)

(def-derived Lbb Lflat-set!
  (Body [b]
        - (locals (??x*) ?t)
        + (locals (??x*) ?blocks))
  (Blocks [blocks]
          + (labels ((?:* [?l* ?t*])) ?l))
  (Tail [t]
        - ?tr
        - (?binop ?tr0 ?tr1)
        - (alloc ?tr)
        - (mref ?tr0 ?tr1)
        - (call ?tr ??tr*)
        - (if ?pr0 ?t1 ?t2)
        + (return ?tr)
        + (goto ?l)
        + (if (?relop ?tr0 ?tr1) (?l0) (?l1)))
  - Pred
  (Effect [ef]
          - (nop)
          - (if ?pr0 ?ef1 ?ef2)
          - (begin ??ef* ?ef))
  (Rhs [rhs]
       + (tail-call ?tr ??tr*)))

(def-derived Lssa Lbb
  (Rhs [rhs]
       + (phi (?:* [?tr* ?l*]))))

(def-derived Lflat-funcs Lssa
  (Program [prog]
           - (letrec ((?:* [?l* ?f*])) ?b)
           + (letrec ((?:* [?l* ?f*])) ??c* ?c))
  - Body
  - Blocks
  - Effect
  - Tail
  (Lambda [f]
          - (lambda (??x*) ?b)
          + (lambda (??x*) ??c* ?c))
  (Code [c]
        + (label ?l)
        + (set! ?x ?rhs)
        + (mset! ?tr0 ?tr1 ?tr2)
        + (call ?tr ??tr*)
        + (goto ?l)
        + (return ?tr)
        + (if (?relop ?tr0 ?tr1) (?l0) (?l1))))
