(ns demo
  (:require [pattern :refer :all]
            [pattern.match.core :refer [register-matcher unregister-matcher
                                        compile-pattern*]]

            [simplify-test :refer [expr<?]]
            [pattern.match.predicator :refer [*pattern-replace* make-abbr-predicator]]))


(rule '(= ?a ?b) (when (not= a b) (success false)))

(rule-list (rule '(= ?a ?b)
             (when (not= a b) (success false))))

((rule '(?:seq ??e* ?e0 ?e1)
   (sub (?e0 ?e1 ??e*)))
 (range 10))
((rule '(set! ?x1 (| (? _ int?) (? _ symbol?)))
   (success nil))
 '(set! a b))

((rule-list
   (rule '?x (sub (+ ?x ?x)))
   (rule '(+ ?x ?x) (sub [double ?x])))
 '(+ 1 1))

((in-order
   (rule '(+ ?x ?x) 'nooo)
   (rule '?x (sub (+ ?x ?x)))
   (rule '(+ ?x ?x) (sub [double ?x])))
 '(+ 1 1))

((in-order
   (rule 1 2)
   (rule 2 3)
   (rule 9 1)
   (rule 3 4))
 9)

((in-order
   (rule 1 2)
   (rule 2 3)
   (rule 9 1)
   (rule 3 4))
 1)

((rule-list
   (rule 1 2)
   (rule 2 3)
   (rule 9 1)
   (rule 3 4))
 1)

((rule-list
   (rule 1 2)
   (rule 2 3)
   (rule 9 1)
   (rule 3 4))
 2)

((iterated (rule-list
             (rule 1 2)
             (rule 2 3)
             (rule 9 9)
             (rule 3 4)
             (rule 4 4)
             (rule '?x (- x 1))))
 100)

((iterated (in-order
             (rule 1 2)
             (rule 2 3)
             (rule 9 9)
             (rule 3 4)
             (rule 4 4)
             (rule '?x (- x 1))))
 100)

;; predicate with arg
((rule '(? x = 3) 4) 0)
((rule '(? x = 3) 4) 3)

((directed
   (rule-list
     (rule '(+ (?:* ?->a ??!->b))
       ;; ?->a produces a sequence because it's captured within ?:*
       (sub (+ (+ ??a c) ??b)))
     ;; ??b within the ?:* match above produces a list of vectors of pattern.
     (rule '[?x] (* (descend 10) (descend x)))
     (rule '(* ??->a)
       (sub (* (+ ?a c))))
     (rule '(? x int?) (inc x))))
 '(+ 1 2))

((directed str
   (rule-list [(rule '(+ (?:* ?->a ??!->b))
                 (sub (+ (+ ??a c) ??b)))
               (rule '[?x] (* (descend 10) (descend x)))
               (rule '(* ??->a)
                 (sub (* (+ ?a c))))
               (rule '(? x int?) (inc x))]))
 '(+ 1 2))

((directed str
   (rule-list [(rule '(+ (?:* ?>->a ??!>->b))
                 (sub (+ (+ ??a c) ??b)))
               (rule '[?x] (* (descend 10) (descend x)))
               (rule '(* ??>-a)
                 (sub (* (+ ?a c))))
               (rule '(? x int?) (inc x))]))
 '(+ 1 2))

((directed str
   (rule-list [(rule '(+ ?->>-a ??!>->b)
                 (sub (+ (+ ?a c) ??b)))
               (rule '(? x int?) (* 2 x))]))
 '(+ 1 2 3 4))

((directed str
   (rule-list [(rule '(+ ?>->a ??>-!b)
                 (sub (+ (+ ?a c) ??b)))
               (rule '(? x int?) (* 2 x))]))
 '(+ 1 2 3 4))


;; Call rule with success and failure continuations:
(let [pred (every-pred number? pos?)
      rules [(rule '(+ (? x ~pred) ?y)
               (let [n (dec x)]
                 (sub (+ (+ ?n ?x) (+ ?n ?y)))))
             (rule '(? x pos-int?) (dec x))]
      rl (rule-list rules)
      ro (in-order rules)
      rs1 (on-subexpressions rl)
      rs2 (simplifier rl)]
  [(rl '[(+ 3.0 (+ 2.0 2))] nil (fn [a e f] a) (fn [] 'no-luck))
   (ro '[(+ 3.0 (+ 2.0 2))] nil (fn [a e f] a) (fn [] 'no-luck))
   (rs1 '[(+ 3.0 (+ 2.0 2))] nil (fn [a e f] a) (fn [] 'hmmm))
   (rs2 '[(+ 3.0 (+ 2.0 2))] nil (fn [a e f] a) (fn [] 'hmmm))])


;; return the original value if unchanged
((on-subexpressions
   (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
               (rule '(+ ?a ?b ?c)
                 (sub (+ ?a (+ ?b ?c))))]))
 '(* 1 2 3))

;; If this were allowed to retry deeper subexpressions again it would be able
;; to reduce it further.
((on-subexpressions
   (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
               (rule '(+ ?a ?b ?c)
                 (sub (+ ?a (+ ?b ?c))))]))
 '(+ 1 (+ 2
         (+ 3 4)
         (+ 1 2))))

((simplifier
   (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
               (rule '(+ ?a ?b ?c)
                 (sub (+ ?a (+ ?b ?c))))]))
 '(+ 1 (+ 2
         (+ 3 4)
         (+ 1 2))))


(let [r (directed
          (rule-list [(rule '(down ?->x))
                      (rule '(up   ?x))
                      (rule '(add ??x) (apply + x))]))]
  [(r '(add 1 2 3))
   (r '(down (add 1 2 3)))
   (r '(up (add 1 2 3)))
   (r '(down (down (add 1 2 3))))
   (r '(up (down (add 1 2 3))))
   (r '(down (up (add 1 2 3))))])



((iterated (rule '(+ ?a ?b)
             (when (pos? a)
               (let [a (dec a)]
                 (sub (+ ?a (+ ?a ?b)))))))
 '(+ 4 (+ x 0)))



((rule-list [(rule '(+ 1 ~(inc 1)))
             (rule '?x "nooo")])
 '(+ 1 2))

((rule-list [(rule '(+ 1 ~(inc 1)) "ok")
             (rule '?x "nooo")])
 '(+ 1 2))

((rule-list [(rule '(+ 1 ~(inc 1)) (list 1 9))
             (rule '?x "nooo")])
 '(+ 1 2))


((rule-list [(rule '(+ 1 ~(inc 1)))
             (rule '?x "nooo")])
 '(+ 1 3))

((rule-list [(rule '(+ 1 ~(inc 1)) "ok")
             (rule '?x "nooo")])
 '(+ 1 3))

((rule-list [(rule '(+ 1 ~(inc 1)) (list 1 9))
             (rule '?x "nooo")])
 '(+ 1 3))


;; env contains last matched datum plus the change made in the handler
((rule '[a ?x] (success x (assoc %env :a x)))
 ['a 1]
 {})

;; env contains last matched datum. The result is the original unmodified.
;; arity-2 success with arity-0 success at the value allows modifying env without modifying the value. This
;; same as (success (success) env):
((rule '[a ?x] (success:env (assoc %env :a x)))
 ['a 1]
 {})

;; no match, no env change
((rule-list [(rule '[a ?x] (success x (assoc %env :a x)))
             (rule '[b ?x] (success x (assoc %env :b x)))])
 ['x 1]
 {})

;; env contains last matched datum plus the change made in the handler
((rule-list [(rule '[a ?x] (success x (assoc %env :a x)))
             (rule '[b ?x] (success x (assoc %env :b x)))])
 ['b 1]
 {})

;; no match, no env change
((in-order [(rule '[a ?x] (success x (assoc %env :a x)))
            (rule '[b ?x] (success x (assoc %env :b x)))])
 ['x 1]
 {})

;; env contains last matched datum plus the change made in the handlers
((in-order [(rule '[a ?x] (success ['b 2] (assoc %env :a x)))
            (rule '[b ?x] (success x (assoc %env :b x)))])
 ['a 1]
 {})

;; env contains last matched datum plus the change made in the handlers
((in-order [(rule '[a ?x] (success ['b 2] (assoc %env :a x)))
            (rule '[b ?x] (success x (assoc %env :b x)))
            (rule '[c ?x] 123)])
 ['a 1]
 {})

;; env contains the last matched datum plus the change made in the handlers
((in-order [(rule '[a ?x] (success ['b 2] (assoc %env :a x)))
            (rule '[b ?x] (success ['c 99] (assoc %env :b x)))
            (rule '[c ?x] 123)])
 ['a 1]
 {})


;; no matches, no changes
((on-subexpressions (rule-list [(rule '(- ??x) (success:env (assoc %env :+ x)))
                                (rule '(/ ??x) (success:env (assoc %env :* x)))]))
 '(* (* (+ 4)))
 {})

;; no changes, env modified
((on-subexpressions (rule-list [(rule '(+ ??x) (success:env (assoc %env :+ x)))
                                (rule '(* ??x) (success:env (assoc %env :* x)))]))
 '(* (* (+ 4)))
 {})

;; result changed, env modified
((on-subexpressions (rule-list [(rule '(+ ??x) (success:env (assoc %env :+ x)))
                                (rule '(* ??x) (success:env (assoc %env :* x)))
                                (rule '(? x int?) (inc x))]))
 '(* (* (+ 4)))
 {})

((iterated (rule '(? x < 10)
             (success (inc x)
               (update %env :x (fnil conj []) x))))
 2)

((iterated (rule '(? x < 10)
             (success (inc x)
               (update %env :x (fnil conj []) x))))
 2
 {})

((iterated (rule '(? x < 10)
             (success (inc x)
               (update %env :x (fnil conj []) x))))
 12
 {})

((simplifier
   (rule '(& (? x int?) (? x < 10))
     (success (inc x)
       (update %env :x (fnil conj []) x))))
 [8 5])

((simplifier
   (rule-list [(rule '(& (? x int?) (? x < 10))
                 (success (inc x)
                   (update %env :x (fnil conj []) x)))
               (rule '[?x ?y]
                 (success [x y]
                   (assoc %env :pair [x y])))]))
 [8 5]
 {})

((simplifier
   (rule '(& (? x int?) (? x < 10))
     (success (inc x)
       (update %env :x (fnil conj []) x))))
 [12 11]
 {})


;; directed traversal updates env
((directed
   (rule-list
     [(rule '(+ ?->x ?y ?z)
        (success (sub (?x + ?y + ?z))
          (assoc %env :+ [(:rule/datum %env) x y])))
      (rule '(? x int?) (success (inc x)
                          (update %env :numbers (fnil conj []) x)))]))
 '(+ 10 20 30)
 {})

;; managing env with descend
((directed
   (rule-list
     [(rule '(+ ?->x ?y ?z)
        (let [[y env] (descend y %env)]
          (success (sub (?x + ?y + ?z))
            (assoc env :+ [(:rule/datum %env) x y]))))
      (rule '(? x int?) (success (inc x)
                          (update %env :numbers (fnil conj []) x)))]))
 '(+ 10 20 30)
 {})

;; The env-args metadata on the pattern causes rule to bind x to (:x %env)
(first ((rule ^{:env-args [x]} '(+ ?a 1) (sub (inc (| ?x ?a))))
        '(+ 3 1)
        {:x 99}))

;; This is only able to hit the rule that descends because it iterates after unwrapping the outer Int form
((directed (iterated
             (rule-list
               [(rule '(Int ?x) x)
                (rule '(+ ?->a ?->b)
                  (+ a b))])))
 '(Int (+ 1 (Int (Int (+ (Int 2) (+ (Int 3) (Int 4))))))))

;; The Int form is unwrapped before the next rule is tried
((directed (in-order
             [(rule '(Int ?x) x)
              (rule '(+ ?->a ?->b)
                (+ a b))]))
 '(Int (+ 1 (Int (+ (Int 2) (+ (Int 3) (Int 4)))))))

;; The matched rule does not descend so stops after unwrapping the Int form
((directed (rule-list
             [(rule '(Int ?x) x)
              (rule '(+ ?->a ?->b)
                (+ a b))]))
 '(Int (+ 1 (Int (+ (Int 2) (+ (Int 3) (Int 4)))))))

(first
  ((with-env-args [a b c x]
     (directed
       (rule-list
         (in-order
           [(rule '(+ ?x 1) [a b c x])]))))
   '(+ bound 1)
   {:a 'hi :x 'env}))

((rule '[1 2 ... n]
   'matched)
 '[1 2 2 2 2 2 n])

((rule '(a (?:? ?x) ?b)) '(a b))
((rule '(a (?:? ?x) ?b)) '(a b c))

((rule '(?:chain ?x reverse (?:force x))) '(b a))

(defn person? [x] true)

(def match-person
  (compile-pattern
    '(?:chain
       (? _ person?)
       :address
       (?:map :street ?street :city ?city)
       :country
       (?:map :capital ?city))))

(match-person {:address {:postal-code "M6J 3C9"
                         :street "Dovercourt" :city "Ottawa"
                         :country {:capital "Ottawa"}}})




((rule '[?x (?:chain ?x reverse (?:force x)) ?x])
 '[(b a) (b a) (a b)])

;; This is the ambiguous case where ?:as* is required. ?:as doesn't have the
;; information to know it should capture a sequence. ?:as* guarantees a
;; sequence.
((rule '[1 (?:as z (?:* ?a))] {:got z :for a})
 [1 2])

((rule '[1 (?:as* z (?:* ?a))] {:got z :for a})
 [1 2])

;; ?:as and ?:as* behave the same
((rule '[1 (?:as* z (?:* ?a ?b))] {:got z :for [a b]})
 [1 2 3])

((rule '[1 (?:as z (?:* ?a ?b))] {:got z :for [a b]})
 [1 2 3])

((rule '[1 (?:as z (?:1 2 3))] {:got z})
 [1 2 3])

((rule '[1 (?:as z [2 3])] {:got z})
 [1 2 3])



(defn match-*map
  "Create a ?:*map matcher than can match a key/value pair multiple times."
  [[_ k v] comp-env]
  (compile-pattern*
    (quo `(?:chain
            (? _ ~(some-fn nil? map?))
            seq
            (| nil ((?:* [~k ~v])))))
    comp-env))

(register-matcher '?:*map #'match-*map {:aliases ['?:map*]})


((compile-pattern '[(?:kv ?k ?v)]) [{:a 1 :b 2}])
