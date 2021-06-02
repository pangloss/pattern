(ns matches.nanopass.dialect
  (:require [matches.r3.core :refer [rule make-rule success]]
            [matches.r3.combinators :refer [run-rule iterated rule-list on-subexpressions
                                            on-mutual directed]]
            [matches.match.core :refer [compile-pattern matcher compile-pattern match?
                                        symbol-dict
                                        matcher-type matcher-type-for-dispatch]]
            [matches.r3.rewrite :refer [sub quo]]
            [matches.match.predicator :refer [with-predicates
                                              *pattern-replace*
                                              apply-replacements
                                              match-abbr
                                              make-abbr-predicator]]
            [matches.nanopass.kahn :refer [kahn-sort]]
            [matches.types :refer [->MetaBox ->Ok ok?]]
            [genera :refer [defgenera defgen]]
            matches.matchers
            [clojure.walk :as walk]))

(defonce dialect-tree (atom (make-hierarchy)))
(defonce all-dialects (atom {}))
(def ^:dynamic *from-dialect* nil)
(def ^:dynamic *to-dialect* nil)

(defn terminal-abbrs [dialect]
  (set (map :abbr (vals (:terminals dialect)))))

(defn- make-terminal [terminal abbr]
  (let [pred-name (symbol (name terminal))]
    (if-let [pred (resolve terminal)]
      {:name pred-name
       :abbr abbr
       :predicate pred
       :symbol? (match-abbr abbr)
       :predicator (make-abbr-predicator abbr pred)}
      (throw (ex-info "Unable to resolve predicate" {:pred-name pred-name
                                                     :terminal terminal
                                                     :abbr abbr})))))

(defn- add-remove-terminals [dialect ops names abbrs]
  (reduce (fn [dialect [op n a]]
            (condp = op
              '+ (assoc-in dialect [:terminals (list n a)] (make-terminal n a))
              '- (update dialect :terminals dissoc (list n a))))
          dialect
          (map vector ops names abbrs)))

(defn get-form [dialect form-name]
  (cond (symbol? form-name)
        (let [dialect (if (symbol? dialect)
                        (@all-dialects dialect)
                        dialect)]
          (get-in dialect [:forms form-name]))
        (vector? form-name)
        (apply get-form form-name)
        (and (map? form-name) (:form? form-name))
        form-name))


(defn form-tag
  ([form-name]
   ;; Note that if form-name is [dialect form] it will override *to-dialect*
   (form-tag *to-dialect* form-name))
  ([to-dialect form-name]
   (or (:name (get-form to-dialect form-name))
       (throw (ex-info "Unable to resolve form" {:name form-name :to-dialect (:name to-dialect)})))))

(defn tag [form-name x]
  ;; works with [dialect form-name] style form names
  (if (instance? clojure.lang.IObj x)
    (let [form-name (form-tag form-name)]
      (vary-meta x assoc ::form form-name))
    x))

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
  (if (:=> =>)
    (:=>/from => default)
    default))

(defn =>:to [=> default]
  (if (:=> =>)
    (:=>/to => default)
    default))

(defn =>:type [=> default]
  (if (:=> =>)
    (:=>/type => default)
    default))

(defn tag-result
  "This is a rule combinator that attaches form metadata to the result if the
  rule is successful."
  ([form-name r]
   (tag-result *to-dialect* form-name r))
  ([to-dialect form-name r]
   (let [form (form-tag to-dialect form-name)]
     (with-meta
       (fn do-tag-result
         ([data] (first (run-rule do-tag-result data nil)))
         ([data env] (run-rule do-tag-result data env))
         ([datum env om y n]
          (r datum
             env
             (fn [result env n]
               (if (fn? result)
                 ;; FIXME: 99% sure this condition is not needed
                 (y result env n)
                 (let [result (if (instance? clojure.lang.IObj result)
                                (vary-meta result assoc ::form form)
                                result)]
                   (y result env n))))
             n)))
       (-> (meta r)
           (assoc-in [:rule :tag-result] form)
           (update-in [:rule :match-rule]
                      #(comp (fn [f]
                               (fn [dict]
                                 (let [[r e] (f dict)]
                                   [(tag form r) e])))
                             %)))))))

(defmulti add-form-expr (fn [dialect form expr]
                          (matcher-type expr)))

;; remove ->form-pattern

(defn- form-expr [form expr]
  {:orig-expr expr
   :form-name (:name form)
   :->make-form (fn [{:keys [match]}]
                  (fn make-form [expr]
                    (when (match expr)
                      (tag (:name form) expr))))})

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

(defn finalize-expr [{:keys [->make-form] :as expr} predicators]
  (reduce (fn [expr [k f]]
            (if f
              (assoc expr k (f expr))
              expr))
          (dissoc expr :->make-form)
          (partition 2
                     [:expr #(apply-replacements (:orig-expr %) predicators)
                      :match #(compile-pattern (:expr %))
                      :make-form ->make-form])))

(defn finalize-form [dialect form predicators]
  (let [form-name (:name form)
        ;; if the expr _is_ a terminal, then the terminal _is_ the expr, too.
        eq-terminals (keep (comp :predicate :is-terminal)
                           (:exprs form))
        form? (fn [x]
                (or (= form-name (::form (meta x)))
                    (some #(% x) eq-terminals)))
        ;; same rule (as with terminals above) about other forms that are pulled
        ;; in to be part of this form, but we must do a dependency sort on
        ;; those, so that's deferred to finalize dialect.
        maybe-contains-forms (keep :maybe-is-form (:exprs form))]
    (-> form
        (update :exprs
                (fn [exprs]
                  (reduce (fn [exprs expr]
                            (conj exprs (finalize-expr expr predicators)))
                          []
                          exprs)))
        (assoc :form? form?)
        (assoc :maybe-contains-forms maybe-contains-forms)
        #_ ;; FIXME: these expr-level automatic predicators do seem awful. Is
         ;; there ever a need for them? Don't we just recur rules into exprs? Maybe
         ;; sometimes I'd want expr predicators but I think not usually. Anyway
         ;; for now disabling them seems by far the best approach.
        (assoc :predicator
               ;; Predicator will add $ to the matcher-mode of these matchers to
               ;; indicate the name has attached metadata
               (make-abbr-predicator {:dialect (:name dialect) :form-name form-name}
                                     (:abbr form)
                                     form?)))))

(defn dialect-predicators [dialect]
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
                                    (contained-form? x)))]
                (-> dialect
                    (assoc-in [:forms containing :form?]
                              form?-new)
                    #_ ;; FIXME: see the fixme note in finalize-form on the
                    ;; topic of form predicators being broken
                    (assoc-in [:forms containing :predicator :predicate]
                              form?-new))))
            dialect
            exprs-with-form-predicates)))


(defn make-checker [dialect]
  (let [form-abbrs (set (map :abbr (vals (:forms dialect))))
        mutual-forms (reduce (fn [m {:keys [abbr name] :as f}]
                               (assoc m abbr {:dialect (:name dialect)
                                              :form-name name}))
                             {} (vals (:forms dialect)))
        terminals (vals (:terminals dialect))
        terminal? (if terminals
                    (apply some-fn (map :predicate terminals))
                    (constantly false))
        ok (->Ok)
        ;; TODO: how do I deal with matchers that are just normal loose
        ;; matchers, not binding any particular language form?
        remove-terminals (fn [raw dict]
                           (reduce-kv (fn [dict k v]
                                        (if (= '? (:type (raw k)))
                                          (if (terminal? v)
                                            (assoc dict k ok)
                                            dict)
                                          (assoc dict k
                                                 (if (every? #(or (= ok %) (terminal? %))
                                                             v)
                                                   ok
                                                   v))))
                                      dict dict))
        validator
        (on-mutual
         (:last-form dialect)
         (into {}
               (for [form (vals (:forms dialect))]
                 [(:name form)
                  (directed
                   {:descend {:abbr form-abbrs}
                    :mutual {:abbr (dissoc mutual-forms (:abbr form))}}
                   (rule-list
                    (for [expr (:exprs form)
                          :let [t (matcher-type-for-dispatch (:expr expr))]]
                      (make-rule (:match expr)
                                 (if (= '? t)
                                   (fn [env raw dict]
                                     ;; For ?e exprs, let the rule fall through if not success
                                     (let [dict (remove-terminals raw dict)]
                                       (when (every? #{ok} (vals dict))
                                         ok)))
                                   (fn [env raw dict]
                                     (let [dict (remove-terminals raw dict)]
                                       (if (every? #{ok} (vals dict))
                                         ok
                                         (merge {:fail (:orig-expr expr)}
                                                dict
                                                {:meta (reduce-kv (fn [m k v]
                                                                    (if (ok? v)
                                                                      m
                                                                      (assoc m k (meta v))))
                                                                  {} dict)})))))
                                 (fn [x]
                                   ;; give the handler both the raw matches and the processed version for now
                                   (let [f (symbol-dict x)]
                                     (fn [m] [m (f m)])))
                                 {}))))])))]
    (with-meta
      (fn dialect-checker [expr]
        (let [result (validator expr)
              result (if (= expr result)
                       {:fail (:name dialect) :expr expr}
                       result)]
          (if (map? result)
            (merge {:dialect (:name dialect)}
                   result)
            result)))
      (meta validator))))

(defn finalize-dialect [dialect]
  ;; Predicators are required for top-level forms and for terminals, not for expressions.
  (let [dialect (update dialect :forms
                        (fn [forms]
                          (reduce (fn [forms [form-name form]]
                                    (assoc forms form-name
                                           (finalize-form dialect form (dialect-predicators dialect))))
                                  {}
                                  forms)))
        tas (terminal-abbrs dialect)
        dialect (add-is-form-predicates dialect)
        dialect (assoc dialect :predicators (dialect-predicators dialect))
        _ (when-let [abbr (some tas (map :abbr (vals (:forms dialect))))]
            (throw (ex-info "The same abbr is used for both a terminal and a form" {:abbr abbr})))
        dialect (assoc dialect :validate (make-checker dialect))
        dialect (assoc dialect :valid? (comp ok? (:validate dialect)))]
    (swap! all-dialects assoc (:name dialect) dialect)
    (when (:parent-dialect dialect)
      (swap! dialect-tree derive (:name dialect) (:name @(:parent-dialect dialect))))
    dialect))


;; Each expr must be either a terminal and its matcher type must not be :value
;;
;; Would an unboxing protocol make sense within the matcher? Would need to think through
;; the implications... If something will not match a type that needs to be
;; boxed, we know that in advance... The same kind of pattern rewriting could be used to
;; do the unboxing right in the pattern.

(defn- build-form [dialect form-name abbr ops exprs]
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
                                        '- (vec (remove #(= expr (:orig-expr %)) exprs))))
                                    es
                                    (map vector ops exprs)))))
        (assoc :last-form full-name))))

(defn- remove-form [dialect name]
  (update dialect :forms dissoc name))

(defn- set-entry [dialect name]
  (if (:entry dialect)
    (throw (ex-info "Only one program entry point is allowed" {:entry name}))
    (assoc dialect :entry name)))

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

                   (rule '(?dialect (?name [?abbr] (?:* ?op* ?expr*)) ??more)
                         (continue (build-form dialect name abbr op* expr*)
                                   more))

                   (rule '(?dialect (?name [?abbr] (?:* ?expr*)) ??more)
                         (continue (build-form dialect name abbr (repeat '+) expr*)
                                   more))])))))

(defn- resolve* [x]
  (if (symbol? x) (resolve x) x))

(defn- deref* [x]
  (if (var? x) @x x))

(defn unparse-dialect [dialect]
  `(~'define-dialect ~(:name dialect)
    (~'terminals ~@(map (fn [{:keys [abbr predicate]}]
                          [abbr predicate])
                        (vals (:terminals dialect))))
    ~@(when (:enter dialect)
        [`(~'enter ~(:enter dialect))])
    ~@(map (fn [{:keys [name abbr exprs]}]
             `(~name [~abbr]
               ~@(map :orig-expr exprs)))
           (vals (:forms dialect)))))


(defn ^:no-doc run-derive-dialect [name parent-dialect decls]
  (let [parent-dialect (resolve* parent-dialect)
        dialect (assoc (deref* parent-dialect)
                       :parent-dialect parent-dialect
                       :name name)
        dialect (derive-dialect* (list* dialect (quo decls)))]
    (if (map? dialect)
      (finalize-dialect dialect)
      (throw (ex-info "failed to parse dialect" {:remaining-forms (vec (rest dialect))
                                                 :partial-dialect (unparse-dialect (first dialect))
                                                 :details (first dialect)})))))

(defmacro define-dialect
  "Create a new dialect.

  Both terminals and forms may be defined. The following example creates a
  language with 2 terminals (nsn and tn) and two forms (nsform and ns):

    (define-dialect NS
      (terminals [nsn nsname?]
                 [tn typename?])
      (NsForm [nsform]
              (:require (?:* (| ?nsn:req-symbol
                                [?nsn:req-symbol ??opts])))
              (:import (?:* (| ?nsn:fq-name
                               (?nsn:ns-name ??tn:typenames)))))
      (Namespace [ns]
                 ((?:literal ns) ?nsn:name ??nsform)))

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

(defmacro derive-dialect
  "Create a new dialect based on another one by defining terminals or forms that
  should be added or removed.

  This works essentially the same as [[define-dialect]] but adds a
  parent-dialect argument and makes it possible to prevent inheritance of
  terminals, forms or expressions within forms from the parent dialect by
  prefixing each one with either + or -.

      (derive-dialect D2 NS
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

(defn from-dialect* [dialect f]
  (if dialect
    (let [dialect (if (symbol? dialect)
                    (@all-dialects dialect)
                    dialect)]
      (with-bindings* {#'*from-dialect* dialect
                       #'*pattern-replace* (into (or *pattern-replace* [])
                                                 (:predicators dialect))}
        f))
    (f)))

(defmacro from-dialect [dialect & body]
  `(from-dialect* ~dialect (fn [] ~@body)))

(defn to-dialect* [dialect f]
  (if dialect
    (let [dialect (if (symbol? dialect)
                    (@all-dialects dialect)
                    dialect)]
      (with-bindings* {#'*to-dialect* dialect}
        f))
    (f)))

(defmacro to-dialect [dialect & body]
  `(to-dialect* ~dialect (fn [] ~@body)))

(defmacro dialects [=>dialects & body]
  `(from-dialect (=>:from ~=>dialects nil)
                 (to-dialect (=>:to ~=>dialects nil)
                             ~@body)))

(defn add-form-tags [{:keys [name exprs]} expr]
  ;; TODO: we want the terminal predicates but not the form ones here...
  (let [rules
        (->> exprs
             (map :match)
             (map (fn [match]
                    (make-rule match
                               (fn [{:keys [rule/datum] :as env} dict]
                                 (when-not (symbol? datum)
                                   (when-not (::form (meta datum))
                                     (success (tag name datum) (update env name conj datum)))))))))
        [expr env]
        ((on-subexpressions (rule-list rules)) expr {name []})]
    (clojure.pprint/pprint env)
    expr))

(defn add-tags [dialect expr]
  (reduce (fn [expr form-key]
            (add-form-tags (get-in dialect [:forms form-key])
                           expr))
          expr
          (:form-order dialect)))

(defn validate [dialect expr]
  ((:validate dialect) expr))

(defn valid? [dialect expr]
  ((:valid? dialect) expr))


(comment
  (do
    (defn nsname? [x] (and (symbol? x) (not (namespace x))))
    (defn typename? [x] (and (symbol? x)
                             (not (clojure.string/includes? (name x) "."))))

    (define-dialect NS
      (terminals (nsname nsn)
                 (typename tn))
      (NsForm [nsform]
              (:require (?:* (| ?nsn:req-symbol
                                [?nsn:req-symbol ??opts])))
              (:import (?:* (| ?nsn:fq-name
                               (?nsn:ns-name ??tn:typenames)))))
      (Namespace [ns]
                 ;; Having this look like an actual ns declaration confused
                 ;; nrepl, but we can get around that with ?:literal!
                 ((?:literal ns) ?nsn:name ??nsform)))

    NS

    (derive-dialect D2 NS
                    (terminals + (symbol s)
                               - (nsname nsn)
                               - (typename tn))
                    - NsForm
                    (Expr [e]
                          + (let [(?:* ?s:binding* ?e:bound*)] ??e:body)))

    (walk/postwalk #(or (meta %) %)
                   D2)

    (derive-dialect D3 D2
                    (terminals
                     + (symbol x)
                     + (string mm)
                     + (int pr)
                     - (int x)
                     - (int i))
                    - Namespace
                    (Lambda [l])
                    (Expr [e]
                          + (letr ((?:* [?x* ?e*])) ?body)
                          + (letrec ((?:* [?x* ?e*])) ?body)
                          + ?mm
                          + ?pr
                          + (do ??body)
                          + (fn (?:? ?doc) (?:? ?meta) [??x*] ??body)
                          + (quote ?x)
                          + (if ?e0 ?e1 ?e2)
                          - (let ((?:* [?x* ?e*])) ?body)))

    (derive-dialect D4 D3
                    (terminals - (string mm))
                    - Yo
                    (Expr [e]
                          - ?pr)))

  (meta (:predicator ('Expr (:forms D3))))
  ((:predicate (:predicator (meta (:predicator ('Expr (:forms D3))))))
   (to-dialect 'D4
        (tag 'Expr '(do x))))

  (map meta (:predicators D3))
  (map meta (:predicators D4))

  (meta
   (to-dialect 'D2
         (tag 'Expr '(do x))))

  @all-dialects

  (defn show-with-meta [x]
    (walk/postwalk #(if (meta %) (list % (meta %)) %) x))

  (show-with-meta D3)

  ,)
