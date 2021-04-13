(ns matches.nanopass.pass
  (:require [matches.nanopass.predicator :refer [*pattern-replace*
                                                 make-abbr-predicator
                                                 with-predicates]]
            [matches.nanopass.dialect
             :as d
             :refer [=> ==> ===>
                     =>:from =>:to =>:type
                     get-form
                     tag-result
                     from-dialect]]
            [matches.rule-combinators :as c :refer [on-mutual
                                                    rule-list
                                                    guard
                                                    directed]]
            [matches.rules :refer [rule]]
            [matches.rewrite :refer [quo sub]]))

(defn define-pass [dialects form-rules]
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
        rules (reduce-kv (fn [rules from-type pairs]
                           (let [type-rules
                                 (mapv (fn [[group-type rule]]
                                         (if-let [to-form (when to-dialect
                                                            (=>:to group-type nil))]
                                           (tag-result to-dialect to-form rule)
                                           rule))
                                       pairs)]
                             (assoc rules from-type
                                    (if (= 1 (count type-rules))
                                      (first type-rules)
                                      (rule-list type-rules)))))
                         {} by-from)
        rules (assoc rules ::default (rule-list (concat unconditional conditional)))]
    (on-mutual ::default rules)))

;; There are 2 possible modes of operation for entering. Either unconditionally match against the default type(s), or
;; conditionally match. ===> is unconditional ==> is conditional.
(defmacro defpass
  ([name =>dialects form-rules]
   (assert (= '=> (first =>dialects)))
   (let [[=> from] =>dialects] ;; destructure unevaluated (=> from to) form.
     `(def ~name
        (from-dialect '~from
                      (define-pass ~=>dialects ~form-rules))))))

(def ->expr
  (rule-list [(from-dialect 'D3
                            (rule '(if ?->l:c ?->e:then)
                                  (sub (if ?c ?then nil))))
              (from-dialect 'NS
                            (rule '?nsn
                                  (sub (namespace! ?nsn))))]))
(def ->lambda (rule '(+ 0 ??x) (sub (+ ??x))))

(defpass p (=> NS D2)
  [(=> Namespace Expr) (rule '(ns ?nsn:name ?->nsform) (sub (ns ?name ?nsform)))
   (==> NsForm Expr) ->lambda])

(p '(+ 0 2))
(p (d/tag '[NS NsForm] '(+ 0 2)))
(get-form 'NS 'NsForm)

(meta p)

(comment
  (defn quoted? [x]
    (and (sequential? x) (= 'quote (nth x 0 nil))))

  (make-pass d/NS 'Expr)

  (make-pass d/NS 'Namespace)


  (make)

  (meta (->form '[L1 Expr] '(let [a 1] ?make-pass))))

(comment

  ;; (meta ->expr))

  ;; ((directed ->expr) (sub (if abc.d ~(->form 'D3 'Expr (do hi))))))

  (let [f (from-dialect 'D4
                        (rule '(do ?->y:x)
                              'found))]
    [(meta f)
     (f (sub (do ~(->form 'D4 'Yo ef))))])

  (meta (->form 'D4 'Yo ef))


  (->lambda '(+ 0 3))


  ;; maybe I don't need the explicit var naming like nanopass had? I think that was
  ;; a bit confusing anyway because the names looked like the ones used for catamorphism
  ;; matching bet I don't think they actually are. Here it's clear that the cata's are
  ;; defined in the language def and the input block maps types to rule combinators, while
  ;; the output block matches rule combinators to output types.
  ;; [X] Maybe that output matching isn't even necessary? Instead I could use something like ->expr
  ;; above and just mark that a rule is transforming to an Expr. That's flexible as it could be
  ;; combined in more sophisticated ways.
  ;;
  ;; The input mapping needs to be at the top level because it is defined for a given combination
  ;; of rulesets.

  (defpass dotransform (=> L1 L2)
    [(==> Expr Expr2) (directed ->expr)
     (=> Fn Lambda) ->lambda
     Lambda ->lambda])

  (do-transform (sub (if ~(->form 'D3 'Lambda (+ 0 4)) ~(->form 'D3 'Expr x))))

  (defpass do-transform (=> L1 L2)
    ;; if I want to run some other rule for a given form within the rule block, I can just run it,
    ;; there's no need for explicit support for that... And because the state is global any mutual
    ;; stuff should still just work...
    [(==> Expr NewExpr) (directed
                         (rule-list [(rule '?i)
                                     (tsub L2 'Type
                                           (Int. n))
                                     (rule '(if ?->e:c ?->e:cons)
                                           (tsub L2 'Expr
                                                 (if ?c ?cons nil)))
                                     (rule '(set! ?mutable ?->e)
                                           (let [m (mutable-expr-rule mutable)]
                                             (tsub L2 'Expr (set! ?m ?e))))]))
     (=> Lambda nil) (directed ->lambda)]))
