(ns matches.nanopass.dialect
  (:require [matches.rules :refer [rule rule-fn]]
            [matches.rule-combinators :refer [run-rule iterated rule-list]]
            [matches.match.core :refer [compile-pattern matcher compile-pattern match?]]
            [matches.rewrite :refer [sub quo]]
            [matches.nanopass.predicator :refer [with-predicates
                                                 *pattern-replace*
                                                 apply-replacements
                                                 match-abbr
                                                 make-abbr-predicator]]
            [matches.types :refer [->MetaBox]]
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
  (let [pred-name (symbol (str (name terminal) "?"))]
    (if-let [pred (resolve pred-name)]
      {:name terminal
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
   (form-tag *to-dialect* form-name))
  ([to-dialect form-name]
   (or (:name (get-form to-dialect form-name))
       (throw (ex-info "Unable to resolve form" {:name form-name :to-dialect (:name to-dialect)})))))

(defn tag [form-name x]
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

;; a problem is that patterns are compiled with the predicators and that happens when they
;; are defined so that is pushing me to a very macro-heavy solution downstream from it.
;;
;; That's got me agonizing over syntax but perhaps the real problem is tehre. Maybe
;; I could store the original pattern and allow recompilation with new predicator context?

(comment
  (def NS=>D2 (=>dialect (=> NS D2)
                         (=> Namespace Expr) ->Expr
                         (=>)))

  ((dialect=> NS D2) Expr))

(defn tag-result
  "This is a rule combinator that attaches form metadata to the result if the
  rule is successful."
  ([form-name r]
   (tag-result *to-dialect* form-name r))
  ([to-dialect form-name r]
   (let [form (form-tag to-dialect form-name)]
     (with-meta
       (fn do-tag-result
         ([data] (run-rule do-tag-result data))
         ([datum y n]
          (r datum
             (fn [result n]
               (if (fn? result)
                 (y result n)
                 (let [result (if (instance? clojure.lang.IObj result)
                                (vary-meta result assoc ::form form)
                                result)]
                   (y result n))))
             n)))
       (assoc-in (meta r)
                 [:rule :tag-result] form)))))

(defgenera add-form-expr 3 [& args]
  (throw (ex-info "No add-form-expr matched" {:args args})))

;; remove ->form-pattern

(defn- form-expr [form expr]
  {:orig-expr expr
   :form-name (:name form)
   :->make-form (fn [{:keys [match]}]
                  (fn make-form [expr]
                    (when (match expr)
                      (tag (:name form) expr))))})

(defgen add-form-expr [some? some? list?] [dialect form expr]
  (form-expr form expr))

(defgen add-form-expr [some? some? symbol?] [dialect form expr]
  (if-let [term (some (fn [term]
                        (when ((:symbol? term) expr)
                          term))
                      (vals (:terminals dialect)))]
    (assoc (form-expr form expr)
           :terminal term)
    (throw (ex-info "Simple form expression must be a terminal."
                    {:form (:name form)
                     :expr expr}))))

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
        terminals (keep (comp :predicate :terminal)
                        (:exprs form))
        form? (fn [x]
                (or (= form-name (::form (meta x)))
                    (some #(% x) terminals)))]
    (-> form
        (update :exprs
                (fn [exprs]
                  (reduce (fn [exprs expr]
                            (conj exprs (finalize-expr expr predicators)))
                          []
                          exprs)))
        (assoc :form? form?)
        (assoc :predicator
               ;; Predicator will add $ to the matcher-mode of these matchers to
               ;; indicate the name has attached metadata
               (make-abbr-predicator {:dialect (:name dialect) :form-name form-name}
                                     (:abbr form)
                                     form?)))))

(defn dialect-predicators [dialect]
  (concat (keep :predicator
                (vals (:terminals dialect)))
          (keep :predicator (vals (:forms dialect)))))

(defn finalize-dialect [dialect]
  ;; Predicators are required for top-level forms and for terminals, not for expressions.
  (let [term-predrs (dialect-predicators dialect)
        dialect (update dialect :forms
                        (fn [forms]
                          (reduce (fn [forms [form-name form]]
                                    (assoc forms form-name
                                           (finalize-form dialect form term-predrs)))
                                  {}
                                  forms)))
        dialect (assoc dialect :predicators (dialect-predicators dialect))
        tas (terminal-abbrs dialect)]
    (when-let [abbr (some tas (map :abbr (vals (:forms dialect))))]
      (throw (ex-info "The same abbr is used for both a terminal and a form" {:abbr abbr})))
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
                     :form? (fn form? [x]
                              (= full-name (get (meta x) ::form)))
                     :abbr abbr})]
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
                                    (map vector ops exprs))))))))

(defn- remove-form [dialect name]
  (update dialect :forms dissoc name))

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
       (rule-list [(rule '(?dialect (terminals (?:* ?op* (?name* ?abbr*))) ??more)
                         (continue (add-remove-terminals dialect op* name* abbr*)
                                   more))

                   (rule '(?dialect (terminals (?:* (?name* ?abbr*))) ??more)
                         (continue (add-remove-terminals dialect (repeat '+) name* abbr*)
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

(defn ^:no-doc run-derive-dialect [name parent-dialect decls]
  (let [parent-dialect (resolve* parent-dialect)
        dialect (assoc (deref* parent-dialect)
                       :parent-dialect parent-dialect
                       :name name)
        dialect (derive-dialect* (list* dialect (quo decls)))]
    (if (map? dialect)
      (finalize-dialect dialect)
      (throw (ex-info "failed to parse dialect" {:partial-result dialect})))))

(defmacro define-dialect
  "Create a new dialect.

  Both terminals and forms may be defined. The following example creates a
  language with 2 terminals (nsn and tn) and two forms (nsform and ns):

    (define-dialect NS
      (terminals (nsname nsn)
                 (typename tn))
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
  (let [dialect (if (symbol? dialect)
                  (@all-dialects dialect)
                  dialect)]
    (with-bindings* {#'*from-dialect* dialect
                     #'*pattern-replace* (into (or *pattern-replace* [])
                                               (:predicators dialect))}
      f)))

(defmacro from-dialect [dialect & body]
  `(from-dialect* ~dialect (fn [] ~@body)))

(defn to-dialect* [dialect f]
  (let [dialect (if (symbol? dialect)
                  (@all-dialects dialect)
                  dialect)]
    (with-bindings* {#'*to-dialect* dialect}
      f)))

(defmacro to-dialect [dialect & body]
  `(to-dialect* ~dialect (fn [] ~@body)))

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
