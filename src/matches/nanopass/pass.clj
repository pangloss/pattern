(ns matches.nanopass.pass
  (:require [matches.match.predicator :refer [*pattern-replace*
                                              make-abbr-predicator
                                              with-predicates]]
            [matches.match.core :refer [compile-pattern]]
            [matches.nanopass.dialect
             :as d
             :refer [=> ==> ===>
                     =>:from =>:to =>:type
                     dialects
                     from-dialect]]
            [matches.r3.combinators :as c :refer [on-mutual
                                                  on-subexpressions
                                                  rule-list
                                                  guard
                                                  descend
                                                  directed]]
            [matches.r3.core :refer [rule success]]
            [matches.r3.rewrite :refer [quo sub add-env-args*]]))

(defn get-form [dialect form-name]
  (cond (symbol? form-name)
        (let [dialect (if (symbol? dialect)
                        (@d/all-dialects dialect)
                        dialect)]
          (get-in dialect [:forms form-name]))
        (vector? form-name)
        (apply get-form form-name)
        (and (map? form-name) (:form? form-name))
        form-name))

(defn combine-rules
  "Combine a collection of rule combinators which each handle inputs tagged with
  a specific type and create an [[on-mutual]] rule for them.

  `form-rules` is map of `group-type` to `rule-fn`, or may be a flat list of
  pairs in the typical Clojure style.

  Each `group-type` is one of the arrow expressions `=>` `==>` `===>`. For
  example `(=> FromForm ToForm)`. Arrow length is used to decide which forms
  are used for the entry expression. If any long `===>` arrows are present, they
  will be tried unconditionally of expression type. If they do not match, or if
  there are no long arrows, then if any medium `==>` arrows are present, they
  will be tried, but respecting their input type. If any long or medium arrows
  are present, short `=>` arrows are not tried. If there are only short arrows,
  then they are all treated like medium arrows."
  [dialects form-rules]
  (let [from-dialect (=>:from dialects nil)
        to-dialect (=>:to dialects nil)
        form-rules (if (map? form-rules) form-rules (partition 2 form-rules))
        by-type (group-by (fn [[group-type rule]]
                            (=>:type group-type '=>))
                          form-rules)
        by-from (group-by (fn [[group-type rule]]
                            (=>:from group-type group-type))
                          form-rules)
        unconditional (map second ('===> by-type))
        conditional (map (fn [[group-type rule]]
                           (if-let [form? (:form? (get-form from-dialect (=>:from group-type nil)))]
                             (guard form? rule)
                             rule))
                         (or ('==> by-type)
                             (when-not unconditional
                               ('=> by-type))))
        rules (reduce-kv (fn [rules from-type type-rules]
                           (assoc rules from-type
                                  (if (= 1 (count type-rules))
                                    (first type-rules)
                                    (rule-list type-rules))))
                         {} by-from)
        rules (assoc rules ::default (rule-list (concat unconditional conditional)))]
    (on-mutual ::default rules)))

(def ^:private insert-defn*
  (on-subexpressions (rule '(?:chain (? _ symbol?) name "<>")
                           (if (:found %env)
                             (throw (ex-info "Only one <> marker is allowed." {:name (:name %env)}))
                             (success `(defn ~(:name %env) ~@(:fn-tail %env))
                                      (assoc %env :found true))))))

(defn insert-defn
  "Used by defpass to replace <> with the pass entry function"
  [compiled name fn-tail]
  (let [[form {:keys [found]}] (insert-defn* compiled
                                             {:name name :fn-tail fn-tail})]
    (if found
      form
      (throw (ex-info "No <> marker found." {:name name})))))

(def ^:private just-a-string? (compile-pattern '((? _ string?))))

(defn- arrow? [x]
  (when (and (list? x) (symbol? (first x)))
    (#{"=>" "==>" "===>"} (name (first x)))))

(def ^:private dialectify*
  (on-subexpressions
   (rule-list [(rule `(let-rulefn ?arg ??args)
                     (when-not (arrow? arg)
                       `(let-rulefn* ~(:dialects %env) ~arg ~@args)))])))


(defn dialectify
  "Used by defpass to rewrite let-rulefn to use its dialects"
  [dialects expr]
  (first (dialectify* expr {:dialects dialects})))


(defmacro defpass
  "Define a pass with the given name and dialects. Use
  `(=> FromDialect ToDialect)` to specify the dialect pair.

  This may be used either as a simple pass definition with no function body defined, in
  which case it will define `name` to be the value of the `compiled` argument, which may
  be a rule, [[let-rulefn]], or any other expression.

  Alternately, if a fn-tail is defined then the `compiled` expression must contain `<>`
  exactly once in the location you want the function definition to be inserted. The
  point of this exercise is to allow the rule functions to be precompiled while
  still allowing a clear syntax for defining a pass.

  Example usage:

        (defpass naive-cps (=> LambdaCalc CPS)
          (let-rulefn [(M (=> Expr MExpr)
                          [(rule '(fn [?var] ?expr)
                                  (let [k (gensym 'k)]
                                  (sub (fn [?var ?k] ~(T expr k)))))
                           (rule '(? s symbol?) s)])
                       (T* (=> Expr TExpr) [cont]
                          [(rule '(?:as expr (fn ??_))
                                  `(~cont ~(M expr)))
                           (rule '(? s symbol?)
                                 `(~cont ~(M s)))
                           (rule '(?f ?e)
                                  (let [fs (gensym 'f)
                                        es (gensym 'e)]
                                    (T f (sub (fn [?fs]
                                                ~(T e (sub (fn [?es]
                                                             (?fs ?es ?cont)))))))))])
                       (fn T [expr cont]
                          (first (T* expr {:cont cont})))]
            <>)
          [expr cont]
          (T expr cont))

        (naive-cps '(g a) ''halt)
        ;; => ((fn [f48299] ((fn [e48300] (f48299 e48300 (quote halt))) a)) g)

  In the above example, `M` is a simple rule, but `T*` uses its env to get the
  value of `cont`. The `[cont]` clause in the T* definition causes the rule
  handler to be wrapped in (let [cont (:cont %env)] ...).

  At the end of the definition, the `[expr cont] (T expr cont)` expression gets
  wrapped with `(defn naive-cps ...)`, and the defn is placed at the point
  indicated by `<>`.

  LambdaCalc and CPS are the dialects being transformed between. Expr is a
  form in LambdaCalc and MExpr and TExpr are forms in CPS."
  [name dialects compiled & fn-tail]
  (let [compiled (dialectify '%dialects compiled)]
    (if ((some-fn empty? just-a-string?) fn-tail)
      `(def ~name ~@fn-tail ;; empty or docstryng
         (let [dialects# ~dialects]
           (dialects dialects# ~compiled)))
      `(do (def ~name)
           (let [dialects# ~dialects]
             (dialects dialects#
                       ~(insert-defn (or compiled '<>) name fn-tail)))))))

(defn -add-env-args [rule-list env-args]
  (mapv (fn [rule]
          (first (add-env-args* rule {:env-args env-args})))
        rule-list))

(def rulefn* (rule-list [(rule '(fn ?name ??fn-tail)
                               (when (symbol? name)
                                 {:fn? true
                                  :name name
                                  :fn-tail fn-tail}))
                         (rule '(?name ?types (?:? ?env-args) ?rule-list)
                               (when (and (symbol? name)
                                          (or (nil? types)
                                              (symbol? types)
                                              (arrow? types))
                                          (or (nil? env-args) (vector? env-args))
                                          (vector? rule-list))
                                 {:rule? true
                                  :name name
                                  :types types
                                  :env-args env-args
                                  :rule-list rule-list}))
                         (rule '?expr {:failed? true :expr expr})]))

(defmacro let-rulefn* [dialects rulefns & body]
  (let [info (mapv rulefn* rulefns)
        failed (filter :failed? info)
        info (map (fn [{:keys [name rule? rule-list env-args fn-tail] :as i}]
                    (let [as (gensym name)
                          ds (gensym name)
                          rule-list (when rule-list (-add-env-args rule-list env-args))]
                      (assoc i :atom-sym as
                             :def-sym ds
                             :atom `[~as (atom nil)]
                             :fn `[~name (fn ~name [& args#]
                                           (apply @~as args#))]
                             :def (if rule?
                                     `[~ds (directed (rule-list ~rule-list))]
                                     `[~ds (fn ~name ~@fn-tail)])
                             :reset `(reset! ~as ~ds))))
                  (remove :failed? info))
        form-rules (map (juxt :types :def-sym)
                        (filter :rule? info))
        body (if (seq body) body ['%pass])]
    (if (empty? failed)
      `(let [~@(mapcat :atom info)
             ~@(mapcat :fn info)
             ~@(mapcat :def info)
             ~'%pass (combine-rules ~dialects [~@form-rules])]
         ~@(map :reset info)
         ~@body)
      (throw (ex-info "Some definitions not understood in let-rulefn:"
                      {:failed (mapv :expr failed)})))))

(defmacro let-rulefn
  "This does a simple transformation to allow all of the rules in rule-fns to
  refer to each other. Each rule list is made [[directed]], and all of the rule
  lists are assembled into an [[on-mutual]] set of rules via [[combine-rules]].
  The combined ruleset is bound to `%pass`.

  If no body expressions are provided, this will return `%pass`, otherwise it
  will return the value of the last expression in the body.

  When used inside [[defpass]], this call is rewritten to use [[let-rulefn*]] with
  the dialect pair specified in the pass. If you don't want this behaviour, use
  [[let-rulefn*]] directly."
  [rulefns & body]
  `(let-rulefn* nil ~rulefns ~@body))

;; TODO: maybe a def-rulefn would be better, where each of the mutual fns were
;; exposed as top-level def's? Anyway in most of the passes I've done so far it
;; hasn't been a big deal to just def each part directly and call into them.
;; Usually there is some processing to do anyway, and per-type dispatch outside
;; of visible forms seems pointless since it's easy and much more understandable
;; to add visible forms to distinguish expression types.  so this whole concept
;; seems pretty pointless, except it's pretty nice for auto-generated code, but
;; that works a little differently. See the dialect validity checker.

(comment
  (defpass xyz (=> A B)
    (rule '(+ ?a ?a) (sub (* 2 ?a))))
  (xyz '(+ 9 9))

  (defpass xx-pass '(A B)
    (let [a 1 b 2 c 3] <>)
    "define a pass"
    [a] (if (zero? a)
          (+ b c)
          (+ (xx-pass (dec a)) b c)))
  (xx-pass 4))
