(ns scheme-to-c.passes
  (:use [scheme-to-c.dialects]
        [pattern :refer [sub rule rule-list in-order directed success substitute matcher descend]]
        [pattern.nanopass.dialect :refer [=> ==> ===>]]
        [pattern.nanopass.dialect :refer [=> ==> ===> show-dialect]]
        [pattern.nanopass.pass :refer [defpass let-rulefn]]))

;; NOTE: this is some early naive porting from the scheme-to-c sample compiler
;; done with the nanopass framework. It was never expected to actually run.
;; The compiler-course work is of the same lineage and does work well.

(def immed? (some-fn number? string?))

(defmacro match [in & pairs]
  ;; This macro will cause the patterns to be recompiled on every execution, so it may be a bit slow. Shouldn't be a problem outside loops?
  `((rule-list [~@(map (fn [[pattern handler]]
                         `(rule ~pattern ~handler))
                    (partition 2 pairs))])
    ~in))

(defmacro match!
  "Apparently syntax-case throws on no match, so use this for that"
  [in & pairs]
  {:style/indent 1}
  `(match ~in ~@pairs '?x (throw (ex-info "no match" {:x ~'x}))))

(defmacro errorf "scheme error compatibility because I'm lazy" [who str & args]
  `(throw (ex-info ~str {:args ~(vec args)})))

(defn primitive->primitive-info [x]
  ;; mostly wrong
  (if (map? x)
    x
    {:name x
     :arity :unknown}))

(defn arity-matches? [x y]
  ;; definitely wrong
  (= (:arity (primitive->primitive-info x))
    (:arity (primitive->primitive-info y))))

(defn identifier? [x]
  ;; not sure...
  (and (symbol? x) (namespace x)))

(defn make-var [x] x)

(def primitive?
  "According to the racket docs this is about primitive fns. I guess that's a clojure function in this context?"
  fn?)

(def Let 'let)

(defpass parse-scheme (=> nil Lsrc)
  (let [parse* (fn parse* [e*] (map parse-scheme e*))
        primitive->primitive-transformer
        (memoize
          (fn [x]
            (let [info (primitive->primitive-info x)]
              (fn [env x]
                (match x
                  '(? sym symbol?)
                  (errorf who "primitives are currently only supported in call position")
                  '(?pr ??e*)
                  (if-not (= (:name info) pr)
                    (errorf who "attempting to apply primitive transformer for ~s to call of ~s" (:name info) pr)
                    (if-not (arity-matches? info e*)
                      (errorf who "incorrect number of arguments ~s" (count e*))
                      ;; parse the args
                      (let [parses (map (fn [e] (parse* e env)) e*)]
                        (sub (?info ??parses)))))
                  '(set! ?x ?e)
                  (errorf who "primitives are immutable, ~s cannot be modified with set!" x)
                  '?x
                  (errorf who "unexpected syntax ~s" x))))))
        apply-env (fn apply-env [env x]
                    (cond
                      (env x) (env x)
                      (primitive? x) (primitive->primitive-transformer x)
                      :else (throw (ex-info "unbound" {:x x}))))

         make-var-transformer (fn [sym var]
                                (fn [env x]
                                  (match! [sym x]
                                    '[?id ?id] var
                                    '[?id (?id ??e*)] (sub (?var ~@(map #(parse-scheme % env) e*)))
                                    '[?id (set! ?id ?e)] (sub (set! ?var ~(parse-scheme e env))))))

         extend-env (fn [env x transformer]
                      (assoc env x transformer))

         extend-var-env (fn [env [x var]]
                          (extend-env env x (make-var-transformer x var)))

         extend-var-env* (fn [env x* var*]
                           (reduce extend-var-env
                             env
                             (map vector x* var*)))

         ;; create an initial env with each of the following expressions added as pattern match functions of [env x].
         ;; each group is (group-name [pattern handler] ...)

         ;; If the supplied x matches the pattern (the leading _ is the group-name). If it matches, the handler is called and

         ;; If it's marked with <- or ?:<- the result is wrapped in the output language construct (uses $top-level-value ),
         ;; as is any value that's unquoted into the expression.
         initial-env
         (let [parse-marked-rules (fn [& rules]
                                    (directed parse-scheme (rule-list rules)))
               simple-rules (fn [& rules]
                              (rule-list rules))]
           ;; NOTE: below, >- indicates passing the value through parse-scheme because
           ;;   (directed f ...) maps >- to its f argument.
           {'quote
            (simple-rules (rule '(quote ?d)
                            (if (datum? d)
                              (sub (quote ?d))
                              (errorf who "expected datum, but got ~s" d))))
            'if
            (parse-marked-rules
              (rule '(if ?>-e0 ?>-e1) (sub (if ?e0 ?e1 (?:<- ~'(void-pr)))))
              (rule '(if ?>-e0 ?>-e1 ?>-e2) (sub (if ?e0 ?e1 ?e2))))
            'and
            (parse-marked-rules
              (rule '(and) '(quote true))
              (rule '(and ?>-e) e)
              (rule '(and ?>-e0 ?e1 ??e*)
                (sub (if ?e0
                       ~(descend (sub (and ?e1 ??e*)))
                       (quote false)))))
            'or
            (parse-marked-rules
              (rule '(or) '(quote false))
              (rule '(or ?>-e) e)
              (rule '(or ?>-e0 ?e1 ??e*)
                (let [t (gensym "t")]
                  (sub (let [?t ?e0]
                         (if ?t ?t ~(descend (sub (or ?e1 ??e*)))))))))
            'not
            (parse-marked-rules
              (rule '(not ?e) (sub (if ?e (quote false) (quote true)))))
            'begin
            (parse-marked-rules
              (rule '(begin ?>-e) e)
              (rule '(begin ??>-e* ?>-e) (sub (begin ??e* ?e))))
            'lambda
            (parse-marked-rules
              (rule '(lambda (??x*) ?>-e)
                (let [v* (mapv make-var x*)
                      env (extend-var-env* %env x* v*)]
                  (sub (lambda (??<-v*) ?e))))
              ;; FIXME: >- is called but does not have the env update that happens in the body so it's useless.
              ;; also, env is built and thrown away now because the parse hidden in >- doesn't get recursively fed with it.
              (rule '(lambda (??x*) ??>-e* ?>-e)
                (let [v* (mapv make-var x*)
                      env (extend-var-env* %env x* v*)]
                  (sub (lambda (??<-v*) (?:<- (begin ??e* ?e)))))))
            'let
            (parse-marked-rules
              (rule '(~Let ((?:* [?x0* ?>-e0*])) ?>-e)
                (let [v0* (map make-var x0*)
                      env (extend-var-env* %env x0* v0*)]
                  (sub (?Let ((?:* [?v0* ?e0*])) ?e))))
              (rule '(~Let ((?:* [?x0* ?>-e0*])) ??>-e* ?>-e)
                (let [v0* (map make-var x0*)
                      env (extend-var-env* %env x0* v0*)]
                  (sub (?Let ((?:* [?v0* ?e0*])) (?:<- (begin ??e* ?e)))))))
            'letrec
            (parse-marked-rules
              (rule '(letrec ((?:* [?x0* ?>-e0*])) ?>-e)
                (let [v0* (map make-var x0*)
                      env (extend-var-env* %env x0* v0*)]
                  (sub (letrec ((?:* [?v0* ?e0*]))
                         ?e))))
              (rule '(letrec ((?:* [?x0* ?>-e0*])) ??>-e* ?>-e)
                (let [v0* (map make-var x0*)
                      env (extend-var-env* %env x0* v0*)]
                  (sub (letrec ((?:* [?v0* ?e0*]))
                         (?:<- (begin ??e* ?e)))))))
            'set!
            (rule '(set! ?x ?e)
              (let [t (apply-env %env x)]
                (t %env (sub (set! ?x ?e)))))})]
     (let-rulefn [(parse (===> nil Expr)
                    [(rule '(? imm immed?) (sub (quote ?imm)))
                     ;; if these two rules match, use the rules stored in the env, above.
                     (rule '(? sym ~initial-env) ((apply-env (:env %env) sym) (:env %env) sym))
                     (rule '((? sym ~initial-env) ??e*) ((apply-env (:env %env) sym) (:env %env) (sub (?sym ??e*))))
                     (rule '(?->e ??->e*) (sub (?e ??e*)))
                     (rule '?x (throw (ex-info "expected Expr but got:" {:x x})))])
                  #_ ;; example...
                  (my-group (=> nil Expr) [ir env]
                    [(rule-group [parse other])])]
       <>))
  ;; NOTE: this block must be OUTSIDE of the above let block
  ([ir]
   (parse ir initial-env)))


;;(def immediate?)
(def convert-datum)
(def dialect-parser)

(defpass convert-complex-datum (=> Lsrc Ldatum)
  (let-rulefn [(expr (=> Expr Expr)
                 [(rule '(quote ?d)
                    (if (immediate? d)
                      (success)
                      (let [var (make-var 'tmp) e (convert-datum d)]
                        (success var (-> %env
                                       (update :var conj var)
                                       (update :e conj e))))))])]
    (let [p (vector dialect-parser [expr])]
      <>))
  ([ir]
   (p ir)))

(defrecord FVInfo [lid mask fv*])


#_
(defpass abc (=> A B)
  (let [a 1]
    (let-rulefn ) <>)
  [b] (+ a b))


;; (show-dialect Lsanitized)

(defpass uncover-free (=> Lsanitized Lfree)
  (letfn [(make--fv-info [index] (->FVInfo index 0 nil))
          (record-ref! [x info]
            #_ ;; NO IDEA what this was about, and the when consequent isn't even present...
            (if-let [idx (:slot x)]
              (when (fx<? idx (:lid info)))))
          (set-offsets! [x* indedx])
          ($with-offsets [index x* p])
          (make-fv-info [index])
          (with-offsets [& x])]
    (let-rulefn [(Expr (=> Expr Expr)
                   [index fv-info]
                   [(rule '?x (record-ref! %env fv-info))
                    (rule '(let ((?:* [?x* ?->e*])) ?e)
                      (with-offsets (index x*)
                        (let [[e env] (Expr e %env)]
                          (success (sub (let ((?:* [?x* ?e*])) ?e))
                            env))))
                    (rule '(letrec ((?:* [?x* ?f*])) ?e)
                      (with-offsets (index x*)
                        (let [[e* env] (map (fn [x] (Lambda x %env)) f*)
                              [e env] (Expr e env)]
                          (success (sub (let ((?:* [?x* ?e*])) ?e))
                            env))))])
                 (Lambda (=> Lambda Lambda) [index outer-fv-info]
                   [(rule '(lambda (??x*) ?e)
                      (let [fv-info (make-fv-info index)]
                        (with-offsets (index x*)
                          (let [e (Expr e %env)
                                fv* (:fv* fv-info)]
                            (doseq [fv fv*]
                              (record-ref! fv outer-fv-info))
                            (sub (lambda (??x*) (free (??fv*) ?e)))))))])]
      <>))
  [ir]
  (Expr ir 0 (make-fv-info 0)))

(def make-label)

(defpass convert-closures (=> Lfree Lclosure)
  (letfn [(make-label [x])]
    (let-rulefn [(Expr (===> Expr Expr)
                   [(rule '(letrec ((?:* [?x* ?->f*])) ?->e)
                      (let [free** (mapv (comp :free* meta) f*)
                            l* (map make-label x*)]
                        (sub (letrec ((?:* [?l* ?f*]))
                               (closures ((?:* [?x* ?l* ??free**])) ?e)))))
                    (rule '(?x ??->e*) (sub (?x ?x ??e*)))
                    (rule '(?pr ??->e*) (sub (?pr ??e*)))
                    (rule '(?->e ??->e*)
                      (let [t (make-var 'proc)]
                        (sub (let ([?t ?e]) (?t ?t ??e*)))))])
                 (Lambda (=> Lambda Lambda)
                   [(rule '(lambda (??x*) (free (??x0*) ?->e))
                      (let [cp (make-var 'cp)]
                        (with-meta (sub (lambda (?cp ??x*) (bind-free (?cp ??x0*) ?e)))
                          {:free* x0*})))])])))



;;; //////////////////////////////////////////////////
;;;

(defpass purify-letrec (=> Ldatum Lletrec)
  (letfn [(var-flags-assigned? [x])
          (simple-expr? [e])
          (pure-primitive? [pr])]
    (let [lambda-expr? (rule '(lambda (??x) ?e) true)
          simple-expr? (rule-list
                         (rule ''?i true)
                         (rule '?x (success (not (var-flags-assigned? x))))
                         (rule '(begin ??e) (success (every? simple-expr? e)))
                         (rule '(if ??e) (success (every? simple-expr? e)))
                         (rule '(?pr ??e) (success (and (pure-primitive? pr) (every? simple-expr? e)))))])))
