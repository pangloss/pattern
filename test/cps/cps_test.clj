(ns cps.cps-test
  (:require [matches :refer [defpass let-rulefn
                             rule sub
                             =>
                             on-subexpressions
                             define-dialect derive-dialect
                             from-dialect
                             tag tag-result
                             show-dialect]]))

(define-dialect Loose
  (terminals [var symbol?]
             [s symbol?]
             [x some?])
  (Expr [e]
        ?s
        ?x))

(define-dialect LambdaCalc
  (terminals [var symbol?]
             [s symbol?])
  (Expr [e]
        ?s
        (fn [?var] ?e)
        (?e ?e)))

(define-dialect CPS

  (terminals [var symbol?]
             [s symbol?])
  (MExpr [mexpr]
         ?s
         (fn [?var ?var] ?cont))
  (Cont [cont]
        (fn [?var] ?cont)
        (?mexpr ?mexpr ?cont)
        (?cont ?mexpr)))



(defpass naive-cps (=> LambdaCalc CPS)
  (let-rulefn [(M (=> Expr MExpr)
                  [(tag-result 'MExpr
                               (rule '[fn [?var] ?e:expr]
                                     (let [k (gensym 'k)]
                                       (sub (fn [?var ?k] ~(T expr k))))))
                   (tag-result 'MExpr
                               (rule '?s s))])

               (T* (=> Expr Cont) [rule/datum cont]
                   [(tag-result 'Cont
                                (rule '[fn ??_]
                                      (let [cont (:cont %env)
                                            expr (:rule/datum %env)]
                                        (sub (?cont ~(M expr))))))
                    (tag-result 'Cont
                                (rule '?s
                                      (let [cont (:cont %env)]
                                        (sub (?cont ~(M s))))))
                    (rule '(?e:f ?e)
                          (let [fs (gensym 'f)
                                es (gensym 'e)
                                cont (:cont %env)]
                            (T f (sub (fn [?fs]
                                        ~(T e (sub (fn [?es]
                                                     (?fs ?es ?cont)))))))))])
               (fn T [expr cont]
                 (first (T* expr {:cont cont})))]
    ;; FIXME: %pass is a stupid name. Just let me provide a name.
    ;; FIXME: Provide the whole pass metadata on output. Reconcile that somehow with the metadata of a returned value...
    (with-meta T (meta %pass))))

(defn all-meta [expr]
  (map (fn [x] (when (meta x) [(meta x) x])) (tree-seq seqable? seq expr)))

(meta naive-cps)

(naive-cps '(g a) 'halt)
;; => ((fn [f29695] ((fn [e29696] (f29695 e29696 (quote halt))) a)) g)


;; FIXME: where is my result metadata??
(all-meta (naive-cps '(g a) 'halt))

(all-meta (naive-cps (tag '[LambdaCalc Expr] '(g a))
                     (tag '[LambdaCalc Expr] 'halt)))

;; TODO: I need a tool that takes a dialect and an expression (with an initial form type?) and recursively type annotates it.

(defpass h-o-cps (=> LambdaCalc CPS2)
  (let-rulefn [(T* (=> Expr Cont) [rule/datum k]
                   [(rule '(fn ??_)
                          (k (M datum)))
                    (rule '?s
                          (k (M datum)))
                    (rule '(?e:f ?e)
                          (let [rv (gensym 'rv)
                                cont (sub (fn [?rv] ~(k rv)))]
                            (T f (fn [f*]
                                   (T e (fn [e*]
                                          (sub (?f* ?e* ?cont))))))))])

               (fn T [expr k]
                 (first (T* expr {:k k})))

               (M (=> Expr MExpr)
                  [(rule '(fn [?var] ?e:expr)
                         (let [ks (gensym 'k)]
                           (sub (fn [?var ?ks]
                                  ~(T expr (fn [rv]
                                             (sub (?ks ?rv))))))))
                   (rule '?s s)])]
    T)
  "Higher order transform")

(h-o-cps '(g a) (fn [ans] (sub (halt ?ans))))


(defpass hybrid-cps (=> Loose CPS3)
  (let-rulefn [(T-k* (=> Expr TK) [rule/datum k]
                    [(rule '(| ?s (fn [??_] ??_))
                           (k (M datum)))
                     (rule '(?e:f ?e)
                           (let [rv (gensym 'rv)
                                 cont (sub (fn [?rv] ~(k rv)))]
                             (T-k f (fn [fr]
                                      (T-k e (fn [er]
                                               (sub (?fr ?er ?cont))))))))])
               (fn T-k [expr k]
                 (first (T-k* expr {:k k})))

               (T-c* (=> Expr TC) [rule/datum c]
                     [(rule '(| ?s (fn [??_] ??_))
                            (sub (?c ~(M datum))))
                      (rule '(?e:f ?e)
                            (T-k f (fn [fr]
                                     (T-k e (fn [er]
                                              (sub (?fr ?er ?c)))))))])
               (fn T-c [expr c]
                 (first (T-c* expr {:c c})))

               (M (=> Expr MExpr)
                  [(rule '(fn [?var] ?e:expr)
                         (let [k* (gensym 'k)]
                           (sub (fn [?var ?k*]
                                  ~(T-c expr k*)))))
                   (rule '?s s)])]
    T-c))
;; FIXME: The LambdaCalc dialect fails to match most expr types (maybe because
;; they aren't tagged?) and so fails to do any transforms. Except it seems to
;; allow anything through at rule entry... which is also wrong if it's actually
;; enforcing expression tagging...
;;
;; FIXME: the predicators are useful but confusing -- they need to be more debuggable!

(hybrid-cps '(e ((g (x f)) (x 1))) 'halt)
(hybrid-cps '(g a) 'halt)



(define-dialect ExpandedInput
  (terminals [var symbol?]
             [s symbol?]
             [n number?]
             [str string?])
  (Aexpr [aexpr]
         (fn [??var*] ?expr)
         ?var
         true false
         ?n
         ?str
         nil
         call/ec
         call/cc)
  (Expr [expr]
        ?aexpr
        (begin ??expr*)
        (if ?expr ?expr:then ?expr:else)
        (set! ?var ?expr)
        (letrec [(?:* ?var* ?aexpr*)] ?expr)
        (?prim ??expr)
        (?expr ??expr*))
  (Prim [prim] + - / * =))

ExpandedInput


(define-dialect ExpandedCPS
  (terminals [var symbol?]
             [s symbol?]
             [n number?]
             [str string?])
  (Aexp [aexp]
        (fn [??var*] ?cexp)
        ?var
        true false
        ?n ?str nil)
  (Prim [prim] + - / * =)
  (Cexp [cexp]
        (if ?aexp ?cexp:then ?cexp:else)
        (set-then! ?var ?aexp ?cexp)
        (letrec [(?:* ?var* ?aexp*)] ?cexp)
        ((cps ?prim) ??aexp*)
        (?aexp ??aexp*)))

(defn cps [f]
  (fn [& args]
    ((last args) (apply f (butlast args)))))

(defmacro set-then! [var exp then]
  `(do (swap! ~var ~exp)
       ~then))

(defpass expanded-transform (=> ExpandedInput ExpandedCPS)
  (let-rulefn [(T-k* (=> Expr Cexp) [rule/datum k]
                     [(rule '?aexpr
                            (k (M aexpr)))
                      (rule '(begin ?expr)
                            (T-k expr k))
                      (rule '(begin ?expr ??expr*)
                            (T-k expr (fn [_]
                                        (T-k (sub begin ??expr*) k))))
                      (rule '(if ?expr ?expr:t ?expr:f)
                            (let [rv (gensym 'rv)
                                  cont (sub (fn [?rv] ~(k rv)))]
                              (T-k expr (fn [aexp]
                                          (sub (if ?aexp
                                                 ~(T-c t cont)
                                                 ~(T-c f cont)))))))
                      (rule '(set! ?var ?expr)
                            (T-k expr (fn [aexp]
                                        (sub (set-then! ?var ?aexp
                                                        ~(k nil))))))
                      (rule '(letrec [(?:* ?var:vs ?aexpr:as)] ?expr)
                            (let [as (mapv M as)]
                              (sub (letrec [(?:* ?vs ?as)]
                                           ~(T-k expr k)))))
                      (rule '(?_ ??_)
                            (let [rv (gensym 'rv)
                                  cont (sub (fn [?rv] ~(k rv)))]
                              (T-c datum cont)))])

               (fn T-k [expr k]
                 (first (T-k* expr {:k k})))

               (T-c* (=> Expr Cexp) [c]
                     ;; TODO: work out result types
                     [(rule '?aexpr
                            (sub (?c ~(M aexpr))))
                      (rule '(begin ?expr) (T-c expr c))
                      (rule '(begin ?expr ??expr*)
                            (T-k expr (fn [_]
                                        (T-c (sub (begin ??expr*) c)))))
                      (rule '(if ?expr ?expr:t ?expr:f)
                            ;; We have to bind the cont to avoid a possible code blow-up:
                            (let [ks (gensym 'k)]
                              (sub ((fn [?ks]
                                      ~(T-k expr (fn [aexp]
                                                   (sub (if ?aexp
                                                          ~(T-c t ks)
                                                          ~(T-c f ks))))))
                                    ?c))))
                      (rule '(set! ?var ?expr)
                            (T-k expr (fn [aexp]
                                        (sub (set-then! ?var ?aexp (?c nil))))))
                      ;; Warning: letrec is not hygenic:
                      (rule '(letrec [(?:* ?var:vs ?aexpr:as)] ?expr)
                            (let [as (mapv M as)]
                              (sub (letrec [(?:* ?vs ?as)]
                                           ~(T-c expr c)))))
                      (rule '(?prim:p ??aexpr:es)
                            (T*-k es (fn [ess]
                                       (sub ((cps ?p) ??ess ?c)))))
                      (rule '(?expr:f ??expr:es)
                            (T-k f (fn [fs]
                                     (T*-k es (fn [ess]
                                                (sub (?fs ??ess ?c)))))))])
               (fn T-c [expr c]
                 (first (T-c* expr {:c c})))

               (fn T*-k [exprs k]
                 (if (empty? exprs)
                   (k [])
                   (T-k (first exprs) (fn [hd]
                                        (T*-k (rest exprs) (fn [tl]
                                                             (k (cons hd tl))))))))

               (M (=> Expr Aexp) [rule/datum]
                  [(rule '(fn [??var*] ?body)
                         (let [k (gensym 'k)]
                           (fn [??vars ?k]
                             ~(T-c body k))))
                   (rule '(| call/cc call/ec)
                         (let [f (gensym 'f)
                               cc (gensym 'cc)
                               x (gensym 'x)]
                           (sub (fn [?f ?cc]
                                  (?f (fn [?x _] (?cc ?x))
                                      ?cc)))))
                   (rule '(| ?s ?n ?str true false nil)
                         datum)
                   (rule '?_
                         "umm not what I hoped would happen"
                         #_ (throw (ex-info "Not an aexpr!" {:datum datum})))])]
    [M T-c]))


;; with dialect matchers, a simple recursive matcher on each form can do the type annotation.
;; Just use (success ...) with meta-only changes.


(let [[M T-c] expanded-transform
      ae {:matches.nanopass.dialect/form '[ExpandedInput Aexpr]}
      e  {:matches.nanopass.dialect/form '[ExpandedInput Expr]}]

  (T-c ^e
       '(letrec [f ^ae (λ [n]
                          ^e (if ^e (= n 0)
                               1
                               ^e (* n ^e (f ^e (- n 1)))))]
                ^e (f 5))
       'halt)
  #_
  (T-c '(g a) 'halt))

(all-meta (matches.nanopass.dialect/add-tags
           ExpandedInput
           '(letrec [f (λ [n]
                          (if (= n 0)
                            1
                            (* n (f (- n 1)))))]
                    (f 5))))




(let [[M T-c] expanded-transform
      ae {:matches.nanopass.dialect/form '[ExpandedInput Aexpr]}
      e  {:matches.nanopass.dialect/form '[ExpandedInput Expr]}]

  ;; NOTE this does not work: it just tags everthing {:e true}, etc.
  (all-meta ^e
            '(letrec [f ^ae (λ [n]
                               ^e (if ^e (= n 0)
                                    1
                                    ^e (* n ^e (f ^e (- n 1)))))]
                     ^e (f 5))))






(defpass explicit-hybrid-cps (=> Loose CPS3)
  (let-rulefn [(T-k* (=> Expr TK) [rule/datum k]
                     [(rule '(| (Expr ?s) (Expr (fn [??_] ??_)))
                            (k (M datum)))
                      (rule '(Expr (?e:f ?e))
                            (let [rv (gensym 'rv)
                                  cont (sub (TK (fn [?rv] ~(k rv))))]
                              (T-k f (fn [fr]
                                       (T-k e (fn [er]
                                                (sub (TK (?fr ?er ?cont)))))))))])
               (fn T-k [expr k]
                 (first (T-k* expr {:k k})))

               (T-c* (=> Expr TC) [rule/datum c]
                     [(rule '(| ?s (Expr (fn [??_] ??_)))
                            (sub (TC (?c ~(M datum)))))
                      (rule '(Expr (?e:f ?e))
                            (T-k f (fn [fr]
                                     (T-k e (fn [er]
                                              (sub (TC (?fr ?er ?c))))))))])
               (fn T-c [expr c]
                 (first (T-c* expr {:c c})))

               (M (=> Expr MExpr)
                  [(rule '(Expr (fn [?var] ?e:expr))
                         (let [k* (gensym 'k)]
                           (sub (MExpr (fn [?var ?k*]
                                         ~(T-c expr k*))))))
                   (rule '(Expr ?s)
                         (sub (MExpr ?s)))])]
    T-c))
;; FIXME: The LambdaCalc dialect fails to match most expr types (maybe because
;; they aren't tagged?) and so fails to do any transforms. Except it seems to
;; allow anything through at rule entry... which is also wrong if it's actually
;; enforcing expression tagging...
;;
;; FIXME: the predicators are useful but confusing -- they need to be more debuggable!

(def unexpr
  "Remove all of the type-marker s-exprs"
  (on-subexpressions (rule '((| Expr TC TK MExpr) ?x) x)))

[(unexpr '(Expr ((Expr e)
                 (Expr ((Expr ((Expr g)
                               (Expr ((Expr x)
                                      (Expr f)))))
                        (Expr ((Expr x)
                               (Expr z))))))))
 (unexpr (explicit-hybrid-cps
          '(Expr ((Expr e)
                  (Expr ((Expr ((Expr g)
                                (Expr ((Expr x)
                                       (Expr f)))))
                         (Expr ((Expr x)
                                (Expr z)))))))
          'halt))]


[(unexpr
  '(Expr ((Expr g) (Expr ((Expr a) (Expr x))))))
 (unexpr
  (explicit-hybrid-cps
   '(Expr ((Expr g) (Expr ((Expr a) (Expr x)))))
   'halt))]
