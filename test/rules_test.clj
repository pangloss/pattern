(ns rules-test
  (:require [clojure.test :refer :all]
            matches.rules
            [matches.match.core :as m :refer [matcher pattern-names var-name]]
            [matches.substitute :refer [substitute]]
            [pure-conditioning :as c :refer [manage restart-with handler-cond]]
            [simplify-test :refer [expr<?]]
            [matches.rules :refer [rule rule-fn success]]
            [matches.nanopass.predicator :refer [*pattern-replace* make-abbr-predicator]]
            [matches.rewrite :refer [sub quo pure-pattern]])
  (:use matches.rule-combinators))



(deftest rules-etc
  (is (= false
         (rule-fn (rule '(= ?a ?b) (when (not= a b) (success false)))
                  '(= 2 1))))

  (is (= false
         (rule-fn (rule-list [(rule '(= ?a ?b) (when (not= a b) (success false)))])
                  '(= 2 1)))))

(deftest interesting-rules
  (is (= [8 9  0 1 2 3 4 5 6 7]
         (rule-fn (rule '(?:seq ??e* ?e0 ?e1)
                        '(?e0 ?e1 ??e*)
                        {})
                  (range 10))))
  (is (nil?
       (rule-fn (rule '(set! ?x1 (| (? _ int?) (? _ symbol?)))
                      (success nil))
                '(set! a b)))))

(deftest rule-combinations
  (is (= '(+ (+ 1 1) (+ 1 1))
         (rule-fn (rule-list [(rule '?x '(+ ?x ?x) {})
                              (rule '(+ ?x ?x) '[double ?x] {})])
                  '(+ 1 1))))

  (is (= '[double nooo]
         (rule-fn (in-order [(rule '(+ ?x ?x) 'nooo)
                             (rule '?x '(+ ?x ?x) {})
                             (rule '(+ ?x ?x) '[double ?x] {})])
                  '(+ 1 1))))

  (is (= 1
         (rule-fn (in-order [(rule 1 2)
                             (rule 2 3)
                             (rule 9 1)
                             (rule 3 4)])
                  9)))

  (is (= 4
         (rule-fn (in-order [(rule 1 2)
                             (rule 2 3)
                             (rule 9 1)
                             (rule 3 4)])
                  1)))

  (is (= 2
         (rule-fn (rule-list [(rule 1 2)
                              (rule 2 3)
                              (rule 9 1)
                              (rule 3 4)])
                  1)))

  (is (= 3
         (rule-fn (rule-list [(rule 1 2)
                              (rule 2 3)
                              (rule 9 1)
                              (rule 3 4)])
                  2)))

  (is (= 9
         (rule-fn (iterated (rule-list [(rule 1 2)
                                        (rule 2 3)
                                        (rule 9 9)
                                        (rule 3 4)
                                        (rule 4 4)
                                        (rule '?x (- x 1))]))
                  100)))
  (is (= 3
         (rule-fn (iterated (in-order [(rule 1 2)
                                       (rule 2 3)
                                       (rule 9 9)
                                       (rule 3 4)
                                       (rule 4 4)
                                       (rule '?x (- x 1))]))
                  100))))

(deftest with-restrictions
  (is (= 0 (rule-fn (rule '(? x = 3) 4) 0)))
  (is (= 4 (rule-fn (rule '(? x = 3) 4) 3))))


(deftest with-marked-subex
  (is (= '(+ (+ 2 c) 33)
         ((rule-fn
           (directed
            (rule-list [(rule '(+ (?:* ?->a ??!->b)) '(+ (+ ??a c) ??b) {})
                        (rule '[(? x)] (* (descend 10) (descend x)))
                        (rule '(* ??->a) '(* (+ ?a c)) {})
                        (rule '(? x int?) (inc x))])))
          '(+ 1 2)))))

(deftest rule-styles
  (let [pred (every-pred number? pos?)
        rules [(rule '(+ (? x ~pred) ?y)
                     '(+ (+ ?n ?x) (+ ?n ?y))
                     {'n (dec x)})
               (rule '(? x pos-int?) (dec x))]
        rl (rule-list rules)
        ro (in-order rules)
        rs1 (on-subexpressions rl)
        rs2 (iterated-on-subexpressions rl)]
    (is (= 'no-luck
           (rl '[(+ 3.0 (+ 2.0 2))] (fn [a b] a) (fn [] 'no-luck))))
    (is (= 'no-luck
           (ro '[(+ 3.0 (+ 2.0 2))] (fn [a b] a) (fn [] 'no-luck))))
    (is (= '[(+ (+ 2.0 3.0) (+ 2.0 (+ (+ 1.0 2.0) (+ 1.0 1))))]
           (rs1 '[(+ 3.0 (+ 2.0 2))] (fn [a b] a) (fn [] 'hmmm))))
    (is (= '[(+ (+ (+ (+ 0.0 1.0) (+ 0.0 2.0)) (+ (+ 0.0 1.0) (+ 0.0 3.0)))
                (+ (+ (+ 0.0 1.0) (+ 0.0 2.0))
                   (+ (+ 0.0 1.0)
                      (+ 0.0 (+ (+ (+ 0.0 1.0) (+ 0.0 2.0))
                                (+ (+ 0.0 1.0) (+ 0.0 0)))))))]
           (rs2 '[(+ 3.0 (+ 2.0 2))] (fn [a b] a) (fn [] 'hmmm))))))


(deftest subexpressions
  (testing "return the original value if unchanged"
    (let [datum '(* 1 2 3)]
      (is (identical? datum
                      (rule-fn (on-subexpressions
                                (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
                                            (rule '(+ ?a ?b ?c)
                                                  (sub (+ ?a (+ ?b ?c))))]))
                               datum)))))

  (testing "If this were allowed to retry deeper subexpressions again it would be able to reduce it further."
    (is (= '(+ 1 (+ 2 (+ 7 3)))
           (rule-fn (on-subexpressions
                     (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
                                 (rule '(+ ?a ?b ?c)
                                       (sub (+ ?a (+ ?b ?c))))]))
                    '(+ 1 (+ 2
                             (+ 3 4)
                             (+ 1 2)))))))

  (is (= 13
         (rule-fn (iterated-on-subexpressions
                   (rule-list [(rule '(+ ?a (? b int?)) (+ a b))
                               (rule '(+ ?a ?b ?c)
                                     (sub (+ ?a (+ ?b ?c))))]))
                  '(+ 1 (+ 2
                           (+ 3 4)
                           (+ 1 2)))))))

(def algebra-1
  (rule-fn
   (rule-simplifier [;; Associative law of addition
                     (rule '(+ ?a (+ ?b ?c))
                           (sub (+ (+ ?a ?b) ?c)))
                     ;; Commutative law of multiplication
                     (rule '(* ?b ?a)
                           (when (expr<? a b)
                             (sub (* ?a ?b))))
                     ;; Distributive law of multiplication over addition
                     (rule '(* ?a (+ ?b ?c))
                           (sub (+ (* ?a ?b) (* ?a ?c))))])))

(deftest easy-algebra
  (is (= '(+ (+ 1 2) 3)
         (algebra-1 '(+ 1 (+ 2 3)))))
  (is (= '(+ (* 1 3) (* 1 2))
         (algebra-1 '(* 1 (+ 3 2))))))

(defn all-equal? [xs]
  (and (< 1 (count xs))
       (apply = xs)))

(def algebra-2
  (rule-fn
   (rule-simplifier [;; Sort
                     (rule '((? op #{* +}) ??x)
                           (let [sorted (sort (fn [a b] (cond (= a b) 0
                                                             (expr<? a b) -1
                                                             :else 1))
                                              x)]
                             (when (not= sorted x)
                               (sub (?op ??sorted)))))

                     ;; Sums
                     (rule '(+ ?a) a)
                     (rule '(+ ??a (+ ??b) ??c)
                           (sub (+ ??a ??b ??c)))

                     ;; Products
                     (rule '(* ?a) a)
                     (rule '(* ??a (* ??b) ??c)
                           (sub (* ??a ??b ??c)))

                     ;; Distributive law
                     (rule '(* ??a (+ ??b) ??c)
                           '(+ ??d)
                           {'d (map #(substitute '(* ??a ?x ??c)
                                                 {'x % 'a a 'c c})
                                    b)})

                     (rule '(+ ??a ?x ??b (* (? n number?) ?x) ??c)
                           '(+ ??a ??b (* ?n ?x) ??c)
                           {'n (inc n)})

                     (rule '(+ ??a (* (? n1 number?) ?x) (* (? n2 number?) ?x) ??b)
                           '(+ ??a (* ?n ?x) ??b)
                           {'n (+ n1 n2)})

                     ;; Numerical simplifications
                     (rule '(+ 0 ??x) (sub (+ ??x)))
                     (rule '(+ (? x number?) (? y number?) (?? z))
                           '(+ ?x ??z)
                           {'x (+ x y)})

                     (rule '(* 0 ??x) 0)
                     (rule '(* 1 ??x) (sub (* ??x)))
                     (rule '(* (? x number?) (? y number?) ??z)
                           '(* ?x ??z)
                           {'x (* x y)})

                     (rule '(+ ??a (??! x all-equal?) ??b)
                           '(+ ??a (* ?n ?x) ??b)
                           {'n (count x)
                            'x (first x)})

                     (rule '(* ??a (expt ?x ?e1) (expt ?x ?e2) ??b)
                           (sub (* ??a (expt ?x (+ ?e1 ?e2)) ??b)))
                     (rule '(* ??a ?x ??b (expt ?x ?e) ??c)
                           (sub (* ??a ??b (expt ?x (+ 1 ?e)) ??c)))
                     (rule '(* ??a (??! x all-equal?) ??b)
                           '(* ??a (expt ?x ?n) ??b)
                           {'x (first x)
                            'n (count x)})])))

(deftest predicates
  (let [rs (atom [])
        pred (fn [s] (= 1 (count s)))
        m (rule '(a ((?? v 3) (?? w ~pred))
                    (? x int?)
                    c (?? y) (?? z))
                {:v v :w w :x x :y y :z z})]
    (is (= [{:v [1 2 3], :w [4], :x 2, :y [] :z [4 3 2]}
            {:v [1 2 3], :w [4], :x 2, :y [4] :z [3 2]}
            {:v [1 2 3], :w [4], :x 2, :y [4 3] :z [2]}
            {:v [1 2 3], :w [4], :x 2, :y [4 3 2] :z []}]
           (m ['a [1 2 3 4] 2 'c 4 3 2]
              (fn ok [x try-again]
                (swap! rs conj x)
                (try-again))
              (fn done [] @rs))))))

(deftest expr-ordering
  (is (expr<? '(* a b) '(* y z)))
  (is (not (expr<? '(* y z) '(* a b)))))

(deftest better-algebra
  (is (= '(+ 12 (* 3 x))
         (algebra-2 '(+ (+ 9 (* x 3)) (+ 3)))))
  (is (= '(+ (* b c (expt a 2)) (* a b w x) (* a c y z) (* w x y z))
         (algebra-2 '(* (+ (* a b) (* y z)) (+ (* w x) (* a c))))))
  (is (= '(expt x 5)
         (algebra-2 '(* x x x x x))))
  (is (= '(+ a b c r (* 2 o))
         (algebra-2 '(+ c o o b r a)))))

(defn symfib [x]
  (if (< x 2)
    x
    `(~'+ ~'x ~(symfib (dec x))
      ~(symfib (- x 2)))))

(defn symfactoid [n]
  "(* x y ... (+ x ... 1))"
  (letfn [(countup [m]
            (if (pos? m)
              (list '+ 'x (countup (dec m)) 1)
              0))]
    (if (pos? n)
      (list '* 'x 'y (symfactoid (dec n))
            (countup n))
      1)))

(defn symfact [n]
  (letfn [(countup [m]
            (if (pos? m)
              (list '+ (countup (dec m)) 1)
              0))]
    (if (pos? n)
      (list '* (symfact (dec n))
            (countup n))
      1)))

(deftest fibbish
  ;; I have not verified that these simplifications are correct...
  (is (= '(+ 55 (* 88 x)) (algebra-2 (symfib 10)))))

(deftest factish
  ;; I have not verified that these simplifications are correct...

  (is (= '(* (* (* (* (* (* (* 1
                               (+ 0 1))
                            (+ (+ 0 1) 1))
                         (+ (+ (+ 0 1) 1) 1))
                      (+ (+ (+ (+ 0 1) 1) 1) 1))
                   (+ (+ (+ (+ (+ 0 1) 1) 1) 1) 1))
                (+ (+ (+ (+ (+ (+ 0 1) 1) 1) 1) 1) 1))
             (+ (+ (+ (+ (+ (+ (+ 0 1) 1) 1) 1) 1) 1) 1))
         (symfact 7)))

  (is (= 5040 (algebra-2 (symfact 7))))
  (is (= 5040 (* 1 2 3 4 5 6 7)))

  (is (= '(* x y (* x y (* x y (* x y (* x y (* x y (* x y 1
                                                       (+ x 0 1))
                                                (+ x (+ x 0 1) 1))
                                         (+ x (+ x (+ x 0 1) 1) 1))
                                  (+ x (+ x (+ x (+ x 0 1) 1) 1) 1))
                           (+ x (+ x (+ x (+ x (+ x 0 1) 1) 1) 1) 1))
                    (+ x (+ x (+ x (+ x (+ x (+ x 0 1) 1) 1) 1) 1) 1))
             (+ x (+ x (+ x (+ x (+ x (+ x (+ x 0 1) 1) 1) 1) 1) 1) 1))
         (symfactoid 7)))

  (is (= '(+
           (* 120 (expt x 5) (expt y 5))
           (* 120 (expt x 6) (expt y 5))
           (* 120 (expt x 9) (expt y 5))
           (* 120 (expt x 10) (expt y 5))
           (* 480 (expt x 6) (expt y 5))
           (* 480 (expt x 7) (expt y 5))
           (* 480 (expt x 8) (expt y 5))
           (* 480 (expt x 9) (expt y 5))
           (* 720 (expt x 7) (expt y 5))
           (* 720 (expt x 8) (expt y 5)))
         (algebra-2 (symfactoid 5)))))

(def math
  ;; Don't use this to do your taxes.
  ;;
  ;; NOTE: this uses implicit predicates for ?x and ?y
  (binding [*pattern-replace*
            [(make-abbr-predicator 'x number?)
             (make-abbr-predicator 'y number?)
             (make-abbr-predicator 'comm #{'+ '*})]]
    (rule-fn
     (rule-simplifier
      [(rule '(??a* ?a / ?b ??b*)
             (when (or (seq a*) (seq b*))
               (sub (??a* (?a / ?b) ??b*))))
       (rule '(??a* ?a (?:+ * ?b) ??b*) ;; TODO: not matcher ((?:* ?a* (?:! *)) ?a (?:+ * ?b) (?:* (?:! *) ?b*))
             '(??a* (?a (?:+ * ?b)) ??b*)
             (if (or (and (seq a*)
                          (not= '* (last a*)))
                     (and (seq b*)
                          (not= '* (first b*))))
               {}))
       (rule '(??a* ?b ?comm ?a ??b*)
             (when (expr<? a b)
               (sub (??a* ?a ?comm ?b ??b*))))
       (rule '(??a ?x (?:+ * ?y) ??b)
             '(??a ?r ??b)
             {'r (apply * x y)})
       (rule '(?a / 0) (sub (?a / 0)))
       (rule '(?a / 1) a)
       (rule '(?x / ?y)
             '?r
             {'r (/ x y)})
       (rule '(1 * ?a) a)
       (rule '(0 * ?a) 0)
       (rule '(0 + ?a) a)
       (rule '(?a / ?b)
             (when (= a b) 1))
       (rule '(??a ?x + ?y ??b)
             '(??a ?r ??b)
             {'r (+ x y)})
       (rule '(??a ?x - ?y ??b)
             '(??a ?r ??b)
             {'r (- x y)})
       (rule '(?a) a)]))))

(deftest infix-math
  (is (= 2/3 (math '(3 / 9 * 2))))
  (is (= 0 (math '(3 / 9 * 0))))
  (is (= '(3 / 0) (math '(3 / (9 * 0)))))
  (is (= '(3 / 0) (math '(3 / 0))))
  (is (= '(6 * a * a * b * c) (math '(a * b * c * a * 1 * 2 * 3))))
  (is (= 364 (math '(3 + v / (1 * v) + 3 * 4 * 5 * 6 + (x * 0))))))

(deftest test-pure-pattern
  ;; These patterns collided with the var names within the patterns in
  ;; unquote-pattern and previously caused some recursive nesting within the
  ;; result.
  ;;
  ;; FIXME: before I wrapped the results in `success` the lists were being
  ;; reversed. The only difference now is that sub is not being applied, so it
  ;; must have been causing list reversal somewhere.
  (is (= `(+ [(?s ~'identity)] ~'identity)
         (pure-pattern ``(+ [(?s 0)] 1))))
  (is (= `(+ [(?item ~'identity)] ~'identity)
         (pure-pattern ``(+ [(?item 0)] 1))))
  (is (= `(+ [(?lists ~'identity)] ~'identity)
         (pure-pattern ``(+ [(?lists 0)] 1))))
  (is (= `(+ [(?quoted ~'identity)] ~'identity)
         (pure-pattern ``(+ [(?quoted 0)] 1))))
  (is (= `(+ [(?v ~'identity)] ~'identity)
         (pure-pattern ``(+ [(?v 0)] 1)))))


(deftest test-quo
  ;; TODO: Instead of (quo `(+ ~a)), create a (sub (+ ?a)) macro that makes ?a and
  ;; ??a work exactly like splicing at the codegen level.

  (let [x (range 4)]
    (is (= '(+ #{a b 0 1 2 3})
           (quo `(+ #{a b ~@x}))))

    (is (= '(+ {a b 0 1 2 3})
           ;; dummy in a last key to make the reader happy!
           (quo `(+ {a b ~@x ~@[]}))))

    (is (= '(+ {a b 0 1 2 3})
           (quo `(+ {a b ~(first x) ~@(rest x)}))))

    (is (= '(+ [a b 0 1 2 3])
           (quo `(+ [a b ~@x])))))

  (let [a [1 2 3]]
    (is (= '[(+ [1 2 3])
             (+ [1 2 3 1] [1 2 3])]
           [(quo `(+ ~a))
            (quo `(+ [~@a 1] ~a))]))))


(deftest test-qsub
  (let [a* [99]
        b* []
        c* [1 2]
        xs 5
        ys 9]
    (is (= '(* 99 1 2 (sqrt (* 5 9)))
           (sub (* ??a* ??b* ??c* (sqrt (* ?xs ?ys))))))

    (is (= 1 (sub (?:* ?c*))))
    (is (= 1 (sub (?:+ ?c*))))
    (is (= [1 2] (sub (?:? ?c* ?c*))))
    (is (= [1 2] (sub (?:1 ?c* ?c*))))
    (is (= 1 (sub (?:? ??c*))))
    (is (= 1 (sub (?:1 ??c*))))
    (is (= 5 (sub (?:? ?xs ?ys))))
    (is (= 5 (sub (?:1 ?xs ?ys))))
    (is (= 1 (sub ??c*)))
    (is (= [1 2] (sub ?c*))))

  (testing "and"
    (is (= '[(a b C C 1 2 3 [3 4])]
           (let [a 'a b 'b x true c ['C 'C]]
             (sub [(?a ?b (& ?x 3 (??-> c)) 1 2 3 [3 4])]))))

    (is (= '[(a b 1 2 3 [3 4])]
           (let [a 'a b 'b x false c ['C 'C]]
             (sub [(?a ?b (& ?x 3 (??-> c)) 1 2 3 [3 4])]))))

    (is (= '[(a b [C C] 1 2 3 [3 4])]
           (let [a 'a b 'b x 1 c ['C 'C]]
             (sub [(?a ?b (& ?x (??-> c) [??c]) 1 2 3 [3 4])])))))


  (testing "or"
    (is (= '[(a b true 1 2 3 [3 4])]
           (let [a 'a b 'b x true c ['C 'C]]
             (sub [(?a ?b (| ?x 3 (??-> c)) 1 2 3 [3 4])]))))

    (is (= '[(a b 3 1 2 3 [3 4])]
           (let [a 'a b 'b x false c ['C 'C]]
             (sub [(?a ?b (| ?x 3 (??-> c)) 1 2 3 [3 4])]))))

    (is (= '[(a b C C 1 2 3 [3 4])]
           (let [a 'a b 'b x nil c ['C 'C]]
             (sub [(?a ?b (| ?x (??-> c)) 1 2 3 [3 4])])))))

  (is (= {:a 1 :b [2] :c :c :d [1 [2]]}
         (let [a 1 b [2]]
           (sub (?:map :a ?a :b ?b :c :c :d [?a ?b])))))

  (let [i 1 k :x]
    (is (= [:x] (sub [(?:if keyword? :x "not keyword")])))
    (is (= :x (sub (?:if keyword? :x "not keyword")))))

  (let [a true]
    (is (= '[... :x 1 2 3 true]
           (sub [... (?:when keyword? :x 1 2 3 ?a)])))
    (is (= :x
           (sub (?:when keyword? :x 1 2 3 ?a)))
        "when returning a group it only returns the first element."))

  (let [i 1 k :kw]
    (is (= [1] (sub [(?:if int? ?i ?k)])))
    (is (= [:kw] (sub [(?:if symbol? ?i ?k)])))
    (is (= [1] (sub [(?:if int? ?i)])))
    (is (= [] (sub [(?:if symbol? ?i)])))
    (is (= [1] (sub [(?:when int? ?i)])))
    (is (= [] (sub [(?:when symbol? ?i)])))
    (is (= [1 2 3] (sub [(?:when int? ?i 2 3)])))
    (is (= [] (sub [(?:when symbol? ?i 2 3)]))))

  (testing "What a weird behaviour, but it is consistent and correct, I think!. Group to a pred applies it as arguments..."
    (let [m {:a 1 :b 2} k :a]
      (is (= [:x {:a 1 :b 2} :a]
             (sub [:x (?:if get (?:? ?m ?k) (?:? 111 999))])))
      (let [k :c]
        (is (= [:x 111 999]
               (sub [:x (?:if get (?:? ?m ?k) (?:? 111 999))])))
        (is (= [:x]
               (sub [:x (?:if get (?:? ?m ?k))])))))))

(deftest test-identity-rules
  (let [r (rule-fn
           (directed
            (rule-list [(rule '(down ?->x))
                        (rule '(up   ?x))
                        (rule '(add ??x) (apply + x))])))]
    (is (= 6 (r '(add 1 2 3))))
    (is (= '(down 6)
           (r '(down (add 1 2 3)))))
    (is (= '(up (add 1 2 3))
           (r '(up (add 1 2 3)))))
    (is (= '(down (down 6))
           (r '(down (down (add 1 2 3))))))
    (is (= '(up (down (add 1 2 3)))
           (r '(up (down (add 1 2 3))))))
    (is (= '(down (up (add 1 2 3)))
           (r '(down (up (add 1 2 3))))))))



(deftest test-iterated
  (is (= '(+ 0 (+ 0 (+ 1 (+ 2 (+ 3 (+ x 0))))))
         (rule-fn (iterated (rule '(+ ?a ?b)
                                  (when (pos? a)
                                    (let [a (dec a)]
                                      (sub (+ ?a (+ ?a ?b)))))))
                  '(+ 4 (+ x 0))))))



(deftest unquote-rule-pattern
  (is (= '(+ 1 2)
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)))
                      (rule '?x "nooo")])
          '(+ 1 2))))

  (is (= "ok"
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)) "ok")
                      (rule '?x "nooo")])
          '(+ 1 2))))

  (is (= '(1 9)
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)) '(?a ?b) '{a 1 b 9})
                      (rule '?x "nooo")])
          '(+ 1 2))))


  (is (= "nooo"
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)))
                      (rule '?x "nooo")])
          '(+ 1 3))))

  (is (= "nooo"
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)) "ok")
                      (rule '?x "nooo")])
          '(+ 1 3))))

  (is (= "nooo"
         (rule-fn
          (rule-list [(rule '(+ 1 ~(inc 1)) '(?a ?b) '{a 1 b 9})
                      (rule '?x "nooo")])
          '(+ 1 3)))))
