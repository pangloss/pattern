(ns pattern.nanopass.dialect
  (:require [pattern.r3.core :refer [rule success]]
            [pattern.r3.rule :refer [make-rule run-rule]]
            [pattern.r3.combinators :refer [iterated rule-list on-subexpressions
                                            on-mutual directed]]
            [pattern.match.core :refer [compile-pattern matcher compile-pattern match?
                                        symbol-dict
                                        matcher-type matcher-type-for-dispatch]]
            [pattern.r3.rewrite :refer [sub quo spliced scheme-style rmeta]]
            [pattern.r3.post-process :refer [raw]]
            [pattern.substitute :refer [substitute]]
            [pattern.match.predicator :refer [with-predicates
                                              *pattern-replace*
                                              apply-replacements
                                              match-abbr
                                              make-abbr-predicator]]
            [pattern.nanopass.kahn :refer [kahn-sort]]
            [pattern.types :refer [->MetaBox ->Ok ok? obj? not-meta? meta?]]
            pattern.matchers
            [clojure.walk :as walk]))

(defonce all-dialects (atom {}))
(def ^:dynamic *from-dialect* nil)
(def ^:dynamic *to-dialect* nil)

(defn dialect
  "Look up a dialect if d is a symbol, otherwise return d."
  [d]
  (if (symbol? d)
    (if-let [dialect (@all-dialects d)]
      dialect
      (throw (ex-info "Dialect not found" {:dialect d})))
    d))

(defmacro =>
  ([from]
   `{:=>/from '~from :=> true :=>/type '~'=>})
  ([from to]
   `{:=>/from '~from :=>/to '~to :=> true :=>/type '~'=>}))

(defmacro ==>
  ([from]
   `{:=>/from '~from :=> true :=>/type '~'==>})
  ([from to]
   `{:=>/from '~from :=>/to '~to :=> true :=>/type '~'==>}))

(defmacro ===>
  ([from]
   `{:=>/from '~from :=> true :=>/type '~'===>})
  ([from to]
   `{:=>/from '~from :=>/to '~to :=> true :=>/type '~'===>}))

(defn =>:from [=> default]
  (:=>/from => default))

(defn =>:to [=> default]
  (:=>/to => default))

(defn =>:type [=> default]
  (:=>/type => default))

(defn- terminal-abbrs [dialect]
  (set (map :abbr (vals (:terminals dialect)))))

(defn- make-terminal [terminal abbr]
  (let [[pred-name resolved]
        (if (set? terminal)
          [terminal terminal]
          (let [pred-name (symbol (name terminal))]
            (if-let [pred (resolve terminal)]
              [pred-name pred]
              (throw (ex-info "Unable to resolve predicate" {:pred-name pred-name
                                                             :terminal terminal})))))]
    {:name pred-name
     :abbr abbr
     :predicate resolved
     :symbol? (match-abbr abbr)
     :predicator (make-abbr-predicator abbr resolved)}))

(defn- add-remove-terminals [dialect ops names abbrs]
  (reduce (fn [dialect [op n a]]
            (let [key (list n a)]
              (condp = op
                '+ (assoc-in dialect [:terminals key] (make-terminal n a))
                '- (if (get-in dialect [:terminals key])
                     (update dialect :terminals dissoc key)
                     (throw (ex-info "Removing nonexistent terminal"
                                     {:dialect (:name dialect)
                                      :terminal key}))))))
          dialect
          (map vector ops names abbrs)))

(defmulti ^:private add-form-expr (fn [dialect form expr]
                                    (matcher-type expr)))

(defn- form-expr [form expr]
  {:orig-expr expr
   :form-name (:name form)})

(defmethod add-form-expr :default [dialect form expr]
  (form-expr form expr))

(defmethod add-form-expr '? [dialect form expr]
  (let [fe (form-expr form expr)]
    (if-let [term (some (fn [term]
                          (when ((:symbol? term) expr)
                            term))
                        (vals (:terminals dialect)))]
      (assoc fe :is-terminal term)
      ;; If it's not a terminal, it may be an expr, but we must wait until
      ;; dialect finalization to incorporate it.
      (assoc fe :maybe-is-form expr))))

;; FIXME: when finalizing Simplified Exp, there is not atm predicator
(defn- finalize-expr [expr predicators]
  (reduce (fn [expr [k f]]
            (if f
              (assoc expr k (f expr))
              expr))
          expr
          (partition 2
                     [:expr #(apply-replacements (:orig-expr %) predicators)
                      :match #(compile-pattern (:expr %))])))

(defn- finalize-form [dialect form predicators]
  (let [form-name (:name form)
        ;; if the expr _is_ a terminal, then the terminal _is_ the expr, too.
        eq-terminals (keep (comp :predicate :is-terminal)
                           (:exprs form))
        ;; same rule (as with terminals above) about other forms that are pulled
        ;; in to be part of this form, but we must do a dependency sort on
        ;; those, so that's deferred to finalize dialect.
        maybe-contains-forms (keep :maybe-is-form (:exprs form))
        form
        (-> form
            (update :exprs
                    (fn [exprs]
                      (reduce (fn [exprs expr]
                                (conj exprs (finalize-expr expr predicators)))
                              []
                              exprs))))
        matchers (keep :match (:exprs form))
        form? (if (seq matchers)
                (apply some-fn matchers)
                (constantly true))
        form (-> form
                 (assoc :form? form?)
                 (assoc :maybe-contains-forms maybe-contains-forms))]
    (if (contains? (:flags form) :enforce)
      (assoc form :predicator
             (make-abbr-predicator (:abbr form) form?))
      form)))

(defn- dialect-predicators [dialect]
  (vec
   (concat (keep :predicator
                 (vals (:terminals dialect)))
           (keep :predicator (vals (:forms dialect))))))

(defn- add-is-form-predicates
  "Some forms may contain a simple matcher, ie ?expr which represents another expression. That
  is captured in :maybe-contains-form but the predicate can only be generated in topo order after
  any possible referred form has been created. This function does the topo sort and then amends the
  form predicate to also match the contained form.

  I'm not 100% sure that this behaviour will match the original nanopass framework..."
  [dialect]
  (let [expr-graph
        (map (fn [{form-name :name syms :maybe-contains-forms}]
               (let [forms (map (fn [sym]
                                  (some (fn [{:keys [symbol? name]}]
                                          (when (symbol? sym)
                                            (second name)))
                                        (vals (:forms dialect))))
                                syms)]
                 (if (not-any? nil? forms)
                   (if ((set forms) (second form-name))
                     (throw (ex-info "A simple expression in a form cannot refer to the form itself"
                                     {:dialect (:name dialect)
                                      :form form-name}))
                     [(second form-name) (set forms)])
                   (throw (ex-info "Unable to resolve simple expression to either a terminal or a form"
                                   {:dialect (:name dialect)
                                    :form form-name
                                    :unresolved (vec (keep (fn [[s f]]
                                                             (when-not f s))
                                                           (map vector syms forms)))})))))
             (vals (:forms dialect)))
        expr-graph (into {} expr-graph)
        sorted (reverse (kahn-sort expr-graph))
        exprs-with-form-predicates (keep (fn [containing]
                                           (when-let [contained (seq (expr-graph containing))]
                                             [containing contained]))
                                         sorted)
        dialect (assoc dialect :form-order sorted)]
    (reduce (fn [dialect [containing contained*]]
              (let [->form? #(get-in dialect [:forms % :form?])
                    form? (->form? containing)
                    contained-form? (apply some-fn (map ->form? contained*))
                    form?-new (fn form-or-contained-form? [x]
                                (or (form? x)
                                    (contained-form? x)))
                    dialect (assoc-in dialect [:forms containing :form?]
                                      form?-new)]
                (if (get-in dialect [:forms containing :predicator])
                  (assoc-in dialect [:forms containing :predicator :predicate]
                            form?-new)
                  dialect)))
            dialect
            exprs-with-form-predicates)))

(defn- compile-metadata-patterns [{:keys [predicators forms] :as dialect}]
  (let [predmap (zipmap (map :abbr predicators) predicators)
        predmap (merge (into {} (map (fn [{:keys [abbr form?]}]
                                       [abbr (make-abbr-predicator abbr form?)])
                                     (vals forms)))
                       predmap)
        preds (vals predmap)]
    (reduce (fn [dialect [name {:keys [metadata-pattern abbr] :as form}]]
              (if metadata-pattern
                (let [pattern `(?:map ~@(apply concat metadata-pattern))
                      pattern (apply-replacements pattern preds)]
                  (assoc-in dialect [:forms name :match-metadata]
                            (compile-pattern pattern)))
                dialect))
            dialect
            forms)))

(defn- expr-matcher-with-meta [matcher match-meta]
  (if match-meta
    (compile-pattern `(& ~matcher
                         (?:all-fresh
                          (| (? _ ~not-meta?)
                             (?:chain ?_ meta ~match-meta)))))
    matcher))

(declare make-checker)

(defn- finalize-dialect [dialect]
  ;; Predicators are required for top-level forms and for terminals, not for expressions.
  (let [dialect
        (update dialect :forms
                (fn [forms]
                  (reduce (fn [forms [form-name form]]
                            (assoc forms form-name
                                   (finalize-form dialect form (dialect-predicators dialect))))
                          {} forms)))
        tas (terminal-abbrs dialect)
        ;; FIXME: why finalize all of the forms and then do this? Finalize them in topo order and
        ;; add predicators as I go. Topo order should include possible preds within expressions (at least
        ;; if they are marked :explicit.
        ;; FIXME: enforce topo order (no cycles) for any forms that have the
        ;; :enforce flag including all expr pattern attrs.
        dialect (add-is-form-predicates dialect)
        dialect (compile-metadata-patterns dialect)
        dialect (assoc dialect :predicators (dialect-predicators dialect))
        _ (when-let [abbr (some tas (map :abbr (vals (:forms dialect))))]
            (throw (ex-info "The same abbr is used for both a terminal and a form" {:abbr abbr})))
        dialect (assoc dialect :validate (make-checker dialect))
        dialect (assoc dialect :valid? (comp ok? (:validate dialect)))]
    (swap! all-dialects assoc (:name dialect) dialect)
    dialect))


;; Each expr must be either a terminal and its matcher type must not be :value
;;
;; Would an unboxing protocol make sense within the matcher? Would need to think through
;; the implications... If something will not match a type that needs to be
;; boxed, we know that in advance... The same kind of pattern rewriting could be used to
;; do the unboxing right in the pattern.

(defn- build-form [dialect form-name abbr metadata flags ops exprs]
  (when (re-find #"[^a-z]" (name abbr))
    (throw (ex-info "Invalid abbr character. Use only lower-case a-z characters."
                    {:dialect (:name dialect) :form form-name :abbr abbr})))
  (let [dialect-name (:name dialect)
        full-name [dialect-name form-name]
        form (merge (get-in dialect [:forms form-name]
                            {:exprs []})
                    {:name full-name
                     ;; NOTE: The form? predicate must be rebuilt for every
                     ;; dialect both to capture the updated [dialect form] name,
                     ;; and because form containment rules may change between
                     ;; dialects.
                     :form? (fn form? [x]
                              (= full-name (get (meta x) ::form)))
                     :abbr abbr
                     :flags (set flags)
                     :metadata-pattern metadata
                     :symbol? (match-abbr abbr)})]
    (-> dialect
        (assoc-in [:forms form-name]
                  (update form :exprs
                          (fn [es]
                            (reduce (fn [exprs [op expr]]
                                      (condp = op
                                        '+ (if (some #(= expr (:orig-expr %)) exprs)
                                             exprs
                                             (conj exprs (add-form-expr dialect form expr)))
                                        '- (if (some #(= expr (:orig-expr %)) exprs)
                                             (vec (remove #(= expr (:orig-expr %)) exprs))
                                             (throw (ex-info "Removing nonexistent expression"
                                                             {:dialect (:name dialect)
                                                              :form form-name
                                                              :expr expr})))))
                                    es
                                    (map vector ops exprs)))))
        (assoc :last-form full-name))))

(defn- remove-form [dialect name]
  (update dialect :forms dissoc name))

(defn- set-entry [dialect name]
  (assoc dialect :entry name))

(def ^:private derive-dialect*
  (with-predicates {'dialect map?
                    'op #{'+ '-}
                    'name symbol?
                    'abbr symbol?
                    'expr (complement #{+ -})}
    (letfn [(continue [dialect more]
              (if (seq more)
                (list* dialect more)
                dialect))]
      (iterated
       (rule-list [(rule '(?dialect (terminals (?:* ?op* [?abbr*
                                                          (| ?name*
                                                             (quote ?name*))]))
                                    ??more)
                         (continue (add-remove-terminals dialect op* name* abbr*)
                                   more))

                   (rule '(?dialect (terminals (?:* [?abbr*
                                                     (| ?name*
                                                        (quote ?name*))]))
                                    ??more)
                         (continue (add-remove-terminals dialect (repeat '+) name* abbr*)
                                   more))

                   (rule '(?dialect (entry ?name) ??more)
                         (continue (set-entry dialect name)
                                   more))

                   (rule '(?dialect - ?name ??more)
                         (continue (remove-form dialect name)
                                   more))

                   (rule '(?dialect (?name [?abbr
                                            (?:? (? metadata map?))
                                            (?:* (? flags keyword?))]
                                           (?:* ?op* ?expr*)) ??more)
                         (continue (build-form dialect name abbr metadata flags
                                               op* expr*)
                                   more))

                   (rule '(?dialect (?name [?abbr
                                            (?:? (? metadata map?))
                                            (?:* (? flags keyword?))]
                                           (?:* ?expr*)) ??more)
                         (continue (build-form dialect name abbr metadata flags
                                               (repeat '+) expr*)
                                   more))])))))

(defn- resolve* [x]
  (if (symbol? x) (resolve x) x))

(defn- deref* [x]
  (if (var? x) @x x))

(declare show-dialect)

(defn ^:no-doc run-derive-dialect [name parent-dialect decls]
  (let [parent-dialect (resolve* parent-dialect)
        dialect (assoc (deref* parent-dialect)
                       :parent-dialect parent-dialect
                       :name name)
        dialect (derive-dialect* (list* dialect (quo (scheme-style decls))))]
    (if (map? dialect)
      (finalize-dialect dialect)
      (throw (ex-info "failed to parse dialect" {:remaining-forms (vec (rest dialect))
                                                 :partial-dialect (show-dialect (first dialect))
                                                 :details (first dialect)})))))

(defmacro def-dialect
  "Create a new dialect.

  Both terminals and forms may be defined. The following example creates a
  language with 2 terminals (nsn and tn) and two forms (nsform and ns):

    (def-dialect NS
      (terminals [nsn nsname?]
                 [tn typename?])
      (NsForm [nsform]
              (:require (?:* (| ?nsn:req-symbol
                                [?nsn:req-symbol ??opts])))
              (:import (?:* (| ?nsn:fq-name
                               (?nsn:ns-name ??tn:typenames)))))
      (Namespace [ns :enforce]
                 ((?:literal ns) ?nsn:name ??nsform))
      (entry Namespace))

  The last form is the entry form for conformance unless a formis specifically
  designated by using (entry FormName).

  By default, only terminals are predicated in matchers. If you want a form
  to be enforced, mark it with :enforce.

  This is a somewhat sophisticated macro and as such has a bit of syntax you
  need to understand.

  There are 2 top-level syntax types: terminals declarations and form
  declarations. Terminals are matched objects that do not require any further
  matching, ie. they are leaves of the syntax tree for the dialect. Forms are
  groups of patterns. In order for an IR instance to be valid, every form as it
  is recursively traversed must match one of the patterns and be tagged with the
  form type (ie. NsForm or Namespace in the above example)."
  [name & decls]
  `(def ~name
     '~(run-derive-dialect name nil decls)))

(defmacro def-derived
  "Create a new dialect based on another one by defining terminals or forms that
  should be added or removed.

  This works essentially the same as [[define-dialect]] but adds a
  parent-dialect argument and makes it possible to prevent inheritance of
  terminals, forms or expressions within forms from the parent dialect by
  prefixing each one with either + or -.

      (def-derived D2 NS
        (terminals + (symbol s)
                   - (nsname nsn)
                   - (typename tn))
        - NsForm
        (Expr [e]
              + (let [(?:* ?s:binding* ?e:bound*)] ??e:body)))

  In the above example, 1 new terminal is added, and 2 are removed, the entire
  NsForm form is removed, and a new Expr form is added, adding a let binding. It
  is also possible to remove a pattern expression from a form by replacing the +
  with a -. Forms that are newly added may also omit all of the + symbols as
  well, but within a form all expressions must either be marked with +/- or not
  marked at all."
  [name parent-dialect & decls]
  `(def ~name
     '~(run-derive-dialect name parent-dialect decls)))

(defn show-dialect
  "Show the given dialect with all additions and removals of terminals, forms
  and expressions resolved. This is a useful tool for debugging, especially for
  dialects that go through many layers of derivation."
  [dialect & {:keys [full-names]}]
  (let [dialect (pattern.nanopass.dialect/dialect dialect)]
    `(~'def-dialect ~(:name dialect)
      (~'terminals ~@(map (fn [{:keys [abbr predicate]}]
                            [abbr predicate])
                       (vals (:terminals dialect))))
      ~@(when (:enter dialect)
          [`(~'enter ~(:enter dialect))])
      ~@(map (fn [{:keys [name abbr exprs flags metadata-pattern]}]
               (let [etc (remove nil? (cons metadata-pattern (seq flags)))]
                 `(~(if full-names name (second name)) [~abbr ~@etc]
                   ~@(map :orig-expr exprs))))
          (vals (:forms dialect))))))

(defn from-dialect* [dialect f]
  (if dialect
    (let [dialect (pattern.nanopass.dialect/dialect dialect)]
      (with-bindings* {#'*from-dialect* dialect
                       #'*pattern-replace* (into (or *pattern-replace* [])
                                                 (:predicators dialect))}
        f))
    (f)))

(defmacro from-dialect
  "Wrap a given rule combinator with the dialect. See `dialects`"
  [dialect & body]
  `(from-dialect* ~dialect (fn [] ~@body)))

(defn to-dialect* [dialect f]
  (if dialect
    (let [dialect (pattern.nanopass.dialect/dialect dialect)]
      (with-bindings* {#'*to-dialect* dialect}
        f))
    (f)))

(defmacro to-dialect
  "Wrap a given rule combinator with the dialect. See `dialects`"
  [dialect & body]
  `(to-dialect* ~dialect (fn [] ~@body)))

(defmacro dialects
  "Wrap a given rule combinator definition to specify that those rules transform
  between the given pair of dialects.

  The rules will also make use of all abbr predicates defined within the rule
  (either terminals or expressions that are marked with :enforce)."
  [=>dialects & body]
  `(let [d# ~=>dialects]
     (from-dialect
      (=>:from d# nil)
      (to-dialect
       (=>:to d# nil)
       (let [b# ~@body
             d# (select-keys d# [:=>/from :=>/to])]
         (cond (var? b#) (alter-meta! b# merge d#)
               (obj? b#) (vary-meta b# merge d#)
               :else b#))))))

(defn- make-checker [dialect]
  (let [form-abbrs (set (map :abbr (vals (:forms dialect))))
        mutual-forms (reduce (fn [m {:keys [abbr name] :as f}]
                               (assoc m abbr {:dialect (:name dialect)
                                              :form-name name}))
                             {} (vals (:forms dialect)))
        terminals (vals (:terminals dialect))
        terminals (when terminals (zipmap (map :abbr terminals) terminals))
        terminal? (if terminals
                    (fn [abbr v]
                      (when-let [{:keys [predicate]} (terminals abbr)]
                        (predicate v)))
                    (constantly false))
        ok (->Ok)
        ;; TODO: how do I deal with matchers that are just normal loose
        ;; matchers, not binding any particular language form?
        remove-terminals (fn [raw dict]
                           (reduce-kv (fn [dict k v]
                                        (let [abbr (:abbr (raw k))]
                                          (if (= '? (:type (raw k)))
                                            (if (terminal? abbr v)
                                              (assoc dict k ok)
                                              dict)
                                            (assoc dict k
                                                   (if (every? #(or (= ok %) (terminal? abbr %))
                                                               v)
                                                     ok
                                                     v)))))
                                      dict dict))
        validator
        (on-mutual
         (if-let [e (:entry dialect)]
           (get-in dialect [:forms e :name])
           (:last-form dialect))
         (into {}
               (for [form (vals (:forms dialect))
                     :let [has-meta (:match-metadata form)]]
                 [(:name form)
                  (directed
                   {:descend {:abbr form-abbrs}
                    :mutual {:abbr (dissoc mutual-forms (:abbr form))}}
                   (rule-list
                    (for [expr (:exprs form)
                          :let [t (matcher-type-for-dispatch (:expr expr))]]
                      (make-rule (expr-matcher-with-meta (:match expr) has-meta)
                                 (if (= '? t)
                                   (fn [env raw dict]
                                     ;; For ?e exprs, let the rule fall through if not success
                                     (if (:raw env)
                                       (merge {:orig (:orig-expr expr)}
                                              dict)
                                       (let [dict (remove-terminals raw dict)]
                                         (when (every? #{ok} (vals dict))
                                           ok))))
                                   (fn [env raw dict]
                                     (if (:raw env)
                                       (merge {:orig (:orig-expr expr)}
                                              dict
                                              {:meta (reduce-kv (fn [m k v]
                                                                  (assoc m k (meta v)))
                                                                {} dict)})
                                       (let [dict (remove-terminals raw dict)]
                                         (if (every? #{ok} (vals dict))
                                           ok
                                           (merge {:fail (:orig-expr expr)}
                                                  dict
                                                  {:meta (reduce-kv (fn [m k v]
                                                                      (if (ok? v)
                                                                        m
                                                                        (assoc m k (meta v))))
                                                                    {} dict)}))))))
                                 (fn [x]
                                   ;; give the handler both the raw matches and the processed version for now
                                   (let [f (symbol-dict x)]
                                     (fn [m] [m (f m)])))
                                 nil
                                 {}))))])))]
    (with-meta
      (fn dialect-checker
        ([expr]
         (dialect-checker expr {}))
        ([expr env]
         (let [result (first (validator expr env))
               result (if (= expr result)
                        {:fail (:name dialect) :expr expr :meta (meta expr)}
                        result)]
           (if (map? result)
             (merge {:dialect (:name dialect)}
                    result)
             result))))
      (meta validator))))

(defn validate
  "Validates an expression in the given dialect and either returns `ok` or a
  detailed parse showing all parse errors."
  [dialect expr]
  ((:validate (@all-dialects dialect dialect)) expr))

(defn valid?
  "Returns true if the expr is valid in the given dialect"
  [dialect expr]
  ((:valid? (@all-dialects dialect dialect)) expr))

(defn show-parse
  "Show a detailed view of how the dialect parses a given input, even if it
  parses it successfully."
  [dialect expr]
  ((:validate (@all-dialects dialect dialect)) expr {:raw true}))

(defn- get-forms [dialect forms]
  (if (= :all forms) (keys (:forms dialect)) forms))

(defn descend-into
  "Creates a rule-list based on the valid expressions in the given dialect. The
  rules do not make any change to the expressions they match, but they enable
  correct descent through those expressions.

  Each `form` in the dialect has a list of expressions. You can either specify
  a list of forms to include, or specify `:all`.

  Descent through the forms is based on the `abbr` of the expression. If a
  form's abbreviation is included in the list of `descend-abbrs`, then for each
  included expression, the vars that have that abbr will be descended through.
  If no descend-abbr is provided, the abbr of each selected form will be used.

  Note that terminals are never included in the list by default, but sometimes
  it may be useful to include them in the `descend-abbrs` list.

  Example dialect

      (def-dialect D1
        (Exp [e] (if ?e:cond ?e:then ?e:else) (prg ?p ??e*))
        (Program [p] (program ?e))

  Example usages

      (descend-into D1)
      ;; => rule list with 3 rules, descending into e and p abbrs.

      (descend-into D1 '[Program])
      ;; => rule list just matching (program ?e), but only descending into p
      ;;    abbrs, so really does nothing.

      (descend-into D1 '[Exp] '[p])
      ;; => rule list matching the 2 forms in Exp, but only descending into
      ;;    p abbrs. Equivalent to:
      (rule-list
        (rule '(if ?e0 ?e1 ?e2)) ;; does nothing but prevents other rules from matching
        (rule '(prg ?->p ??e*))) ;; descends into ?->p but otherwise makes no change"
  ([dialect]
   (descend-into dialect :all))
  ([dialect forms]
   (let [forms (get-forms dialect forms)]
     (descend-into dialect forms (into #{}
                                   (map #(get-in dialect [:forms % :abbr]))
                                   forms))))
  ([dialect forms descend-abbrs]
   (let [forms (get-forms dialect forms)
         abbrs (set descend-abbrs)]
     ;; TODO: should I filter out expressions that would not match any descend rules?
     (->> forms
       (mapcat #(get-in dialect [:forms % :exprs]))
       (remove :is-terminal)
       (keep (fn [{:keys [match orig-expr] :as x}]
               (when match
                 (vary-meta
                   (eval
                     `(raw (rule '~orig-expr
                             (let [value# (sub ~orig-expr)]
                               (success
                                 (if (meta? value#)
                                   (with-meta value# (rmeta))
                                   value#))))))
                   assoc-in [:rule :descend :abbr]
                   abbrs))))))))
