(ns demo.algebra
  (:require [pattern :refer :all]
            [simplify-test :refer [expr<?]]))

(def algebra-1
  (rule-simplifier [;; Associative law of addition
                    (rule '(+ ?a (+ ?b ?c))
                          (sub (+ (+ ?a ?b) ?c)))
                    ;; Commutative law of multiplication
                    (rule '(* ?b ?a)
                          (when (expr<? a b)
                            (sub (* ?a ?b))))
                    ;; Distributive law of multiplication over addition
                    (rule '(* ?a (+ ?b ?c))
                          (sub (+ (* ?a ?b) (* ?a ?c))))]))

(algebra-1 '(+ 1 (+ 2 3)))
(algebra-1 '(* 1 (+ 3 2)))

(defn every-equal? [xs]
  (and (< 1 (count xs))
       (apply = xs)))

(def algebra-2
  (rule-simplifier ;; Sort
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
      (sub (+ ~@(map (fn [x] (sub (* ??a ?x ??c))) b))))

    (rule '(+ ??a ?x ??b (* (? n number?) ?x) ??c)
      (sub (+ ??a ??b (* ~(inc n) ?x) ??c)))

    (rule '(+ ??a (* (? n1 number?) ?x) (* (? n2 number?) ?x) ??b)
      (sub (+ ??a (* ~(+ n1 n2) ?x) ??b)))

    ;; Numerical simplifications
    (rule '(+ 0 ??x) (sub (+ ??x)))
    (rule '(+ (? x number?) (? y number?) (?? z))
      (sub (+ ~(+ x y) ??z)))

    (rule '(* 0 ??x) 0)
    (rule '(* 1 ??x) (sub (* ??x)))
    (rule '(* (? x number?) (? y number?) ??z)
      (sub (* ~(* x y) ??z)))

    (rule '(+ ??a (??! x (on-all every-equal?)) ??b)
      (sub (+ ??a (* ~(count x) ~(first x)) ??b)))

    (rule '(* ??a (expt ?x ?e1) (expt ?x ?e2) ??b)
      (sub (* ??a (expt ?x (+ ?e1 ?e2)) ??b)))
    (rule '(* ??a ?x ??b (expt ?x ?e) ??c)
      (sub (* ??a ??b (expt ?x (+ 1 ?e)) ??c)))
    (rule '(* ??a (??! x (on-all every-equal?)) ??b)
      (sub (* ??a (expt ~(first x) ~(count x)) ??b)))))


;; Getting all possible matches
(let [rs (atom [])
      pred (fn [s] (= 1 (count s)))
      m (rule '(a ((?? v 3) (?? w (on-all ~pred)))
                 (? x int?)
                 c (?? y) (?? z))
          {:v v :w w :x x :y y :z z})]
  (m ['a [1 2 3 4] 2 'c 4 3 2]
    nil
    (fn ok [x env try-again]
      (swap! rs conj x)
      (try-again))
    (fn done [] @rs)))

(algebra-2 '(+ (+ 9 (* x 3)) (+ 3)))
(algebra-2 '(* (+ (* a b) (* y z)) (+ (* w x) (* a c))))
(algebra-2 '(* x x x x x))
(algebra-2 '(+ c o o b r a))

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

;; There are 55 1's and 88 x's in the resulting expression, so the solution is correct.
;; 1111111111111111111111111111111111111111111111111111111
;; xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
(algebra-2 (symfib 10))

(symfact 7)

(algebra-2 (symfact 7))

(symfactoid 7)

(algebra-2 (symfactoid 5))

