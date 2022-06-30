(ns simplify-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [pattern.r3.rule :refer [*debug-rules*]]
            [pattern.r3.combinators :refer [rule-list rule-simplifier
                                            iterated]]
            [pattern.r3.core :refer [rule
                                     rule-name]]
            [pattern.match.predicator :refer [*pattern-replace* make-abbr-predicator]]
            [pattern.r3.rewrite :refer [sub quo pure-pattern]]))
;;; Helper functions for an algebraic simplifier

(defn symbol<? [x y]
  (< (compare (name x) (name y)) 0))

(declare expr<?)

(defn seq<? [x y]
  (let [nx (count x)
        ny (count y)]
    (cond (< nx ny) true
          (< ny nx) false
          :else (loop [x x y y]
                  (cond (empty? x) false
                        (expr<? (first x) (first y)) true
                        (expr<? (first y) (first x)) false
                        :else (recur (next x) (next y)))))))

(def expr<?
  (let [types (partition 2 [nil? (constantly nil)
                            number? <
                            symbol? symbol<?
                            seq? seq<?])]
    (fn expr<? [x y]
      (loop [types types]
        (if (seq types)
          (let [[predicate? comparator] (first types)]
            (cond (predicate? x)
                  (if (predicate? y)
                    (comparator x y)
                    true)
                  (predicate? y) false
                  :else (recur (next types))))
          (throw (ex-info "Unknown expresion type" {:expr<? [x y]})))))))

(defn sort-expressions [x]
  (sort (fn [a b] (cond (= a b) 0
                       (expr<? a b) -1
                       :else 1))
        x))

(defn unary-elimination [& ops]
  (rule-name :unary-elimination
             (rule `((? op ~(set ops)) ?x)
                   x)))

(defn constant-elimination [op constant]
  (rule-name :constant-elimination
             (rule `(~op ??items)
                   (let [items (remove #{constant} items)]
                     (sub (?op ??items))))))

(defn constant-promotion [op constant]
  (rule-name :constant-promotion
             (rule `(~op ??x*)
                   (when (some #(= % constant) x*)
                     (sub (?op ?constant))))))

(defn associative [& ops]
  (let [op-set (into #{} ops)]
    (iterated
     (rule '((? op ~op-set) ??a (?op ??b) ??c)
           (sub (?op ??a ??b ??c))))))

(defn commutative [& ops]
  (rule-name :commutative
             (rule `((? op ~(set ops)) ??exprs)
                   (let [sorted (sort-expressions exprs)]
                     (when (not= sorted exprs)
                       (sub (?op ??sorted)))))))

(defn idempotent [& ops]
  (rule-name :idempotent
             (rule `((? op ~(set ops)) ??exprs)
                   (let [exprs (distinct exprs)]
                     (sub (?op ??exprs))))))

;; IDEA: do something like unquote-pattern to drop namespaces from syntax-quote

(def integral? int?)

(def exponent-contract
  (rule-simplifier
   [(rule '(expt (expt ?op (? m integral?))
                 (? n integral?))
          (let [n+m (+ n m)]
            (sub (expt ?op ?n+m))))
    (rule '(* ??pre
              (expt ?op (? n integral?))
              (expt ?op (? m integral?))
              ??post)
          (let [n+m (+ n m)]
            (sub (* ??pre (expt ?op ?n+m) ??post))))
    (rule '(* ??pre
              ?op (expt op (? n integral?))
              ??post)
          (let [n+1 (+ n 1)]
            (sub (* ??pre (expt ?op ?n+1) ??post))))
    (rule '(* ??pre
              (expt op (? n integral?)) ?op
              ??post)
          (let [n+1 (+ n 1)]
            (sub (* ??pre (expt ?op ?n+1) ??post))))
    (rule '(* ??pre ?op ?op ??post)
          (sub (* ??pre (expt ?op 2) ??post)))]))

(defn even-integer? [x]
  (and (int? x) (even? x)))

(defn odd-integer? [x]
  (and (int? x) (odd? x)))



(def simplify-square-roots
  (rule-simplifier
   [(rule '(expt (sqrt ?x) (? n even-integer?))
          (let [n (/ n 2)]
            (sub (expt ?x ?n))))

    (rule '(sqrt (expt ?x (? n even-integer?)))
          (let [n (/ n 2)]
            (sub (expt ?x ?n))))

    (rule '(sqrt (expt ?x (? n odd-integer?)))
          (let [n (/ (dec n) 2)]
            (sub (* (sqrt ?x) (expt ?x ?n)))))

    (rule '(expt (sqrt ?x) (? n odd-integer?))
          (let [n (/ (dec n) 2)]
            (sub (* (sqrt ?x) (expt ?x ?n)))))

    (rule '(/ ?x (sqrt ?x))
          (sub (sqrt ?x)))

    (rule '(/ (sqrt ?x) ?x)
          (sub (/ 1 (sqrt ?x))))

    (rule '(/ (* ??u ?x ??v) (sqrt ?x))
          (sub (* ??u (sqrt ?x) ??v)))

    (rule '(/ (* ??u (sqrt ?x) ??v) ?x)
          (sub (/ (* ??u ??v) (sqrt ?x))))

    (rule '(/ ?x (* ??u (sqrt ?x) ??v))
          (sub (/ (sqrt ?x) (* ??u ??v))))

    (rule '(/ (sqrt ?x) (* ??u ?x ??v))
          (sub (/ 1 (* ??u (sqrt ?x) ??v))))

    (rule '(/ (* ??p ?x ??q)
              (* ??u (sqrt ?x) ??v))
          (sub (/ (* ??p (sqrt ?x) ??q)
                   (* ??u ??v))))

    (rule '(/ (* ??p (sqrt ?x) ??q)
              (* ??u ?x ??v))
          (sub (/ (* ??p ??q)
                   (* ??u (sqrt ?x) ??v))))]))

(def sqrt-expand
  (rule-simplifier
   [;; "distribute the radical sign across products and quotients.
    ;; but doing this may allow equal subexpressions within the
    ;; radicals to cancel in various ways. The companion rule
    ;; sqrt-contract reassembles what remains."

    ;; Scmutils, in each of these expansions, will `assume!`
    ;; that the expressions named ?x and ?y are non-negative
    (rule '(sqrt (* ?x ?y))
          (sub (* (sqrt ?x) (sqrt ?y))))

    (rule '(sqrt (* ?x ?y ??ys))
          (sub (* (sqrt ?x) (sqrt (* ?y ??ys)))))

    (rule '(sqrt (/ ?x ?y))
          (sub (/ (sqrt ?x) (sqrt ?y))))

    (rule '(sqrt (/ ?x ?y ??ys))
          (sub (/ (sqrt ?x) (sqrt (* ?y ??ys)))))]))


(def logexp
  (rule-list
   [(rule '(exp (* (? n integral?) (log ?x)))
          (sub (exp ?x ?n)))
    (rule '(exp (log ?x)) x)
    (rule '(log (exp ?x)) x)
    (rule '(sqrt (exp ?x)) (sub (exp (/ ?x 2))))
    (rule '(log (sqrt ?x)) (sub (* (/ 1 2) (log ?x))))]))

(def magsimp
  (rule-list
   [(rule '(magnitude (* ?x ?y ??ys*))
          (sub (* (magnitude ?x) (magnitude (* ?y ??ys*)))))
    (rule '(magnitude (expt ?x (? n even-integer?)))
          (sub (expt ?x ?n)))]))

(defn positive? [x]
  (and (number? x) (pos? x)))

(defn sqrt-contract
  ([] (sqrt-contract identity))
  ([simplify]
   ;; Ensure that ?x and ?y are positive
   (binding [*pattern-replace* [(make-abbr-predicator 'x positive?)
                                (make-abbr-predicator 'y positive?)]]
     (rule-list
      [(rule '(* ??a* (sqrt ?x) ??b* (sqrt ?y) ??c*)
             (let [xs (simplify x)
                   ys (simplify y)]
               (if (= xs ys)
                 (sub (* ??a* ?xs ??b* ??c*))
                 (sub (* ??a* ??b* ??c* (sqrt (* ?xs ?ys)))))))

       (rule '(/ (sqrt ?x) (sqrt ?y))
             (let [xs (simplify x)
                   ys (simplify y)]
               (if (= xs ys)
                 1
                 (quo `(sqrt (/ ~xs ~ys))))))

       (rule '(/ (* ??a* (sqrt ?x) ??b*) (sqrt ?y))
             (let [xs (simplify x)
                   ys (simplify y)]
               (if (= xs ys)
                 (quo `(* ~@a* ~@b*))
                 (quo `(* ~@a* ~@b* (sqrt (/ ~xs ~ys)))))))

       (rule '(/ (sqrt ?x) (* ??a* (sqrt ?y) ??b*))
             (let [xs (simplify x)
                   ys (simplify y)]
               (if (= xs ys)
                 (quo `(/ 1 (* ~@a* ~@b*)))
                 (quo `(/ (sqrt (/ ~xs ~ys)
                                (* ~@a* ~@b*)))))))

       (rule '(/ (* ??a* (sqrt ?x) ??b*)
                 (* ??c* (sqrt ?y) ??d*))
             (let [xs (simplify x)
                   ys (simplify y)]
               (if (= xs ys)
                 (quo `(/ (* ~@a* ~@b*)
                          (* ~@c* ~@d*)))
                 (quo `(/ (* ~@a* ~@b* (sqrt (/ ~xs ~ys)))
                          (* ~@c* ~@d*))))))]))))

(def canonicalize-partials
  (rule-simplifier
   [(rule '((partial ??i) ((partial ??j) ?f))
          (sub ((* (partial ??i) (partial ??j)) ?f)))
    (rule '((partial ??i) ((* (partial ??j) ??more) ?f))
          (sub ((* (partial ??i) (partial ??j) ??more) ?f)))

    (rule '((expt (partial ??i) ?n) ((partial ??j) ?f))
          (sub ((* (expt (partial ??i) ?n) (partial ??j)) ?f)))

    (rule '((partial ??i) ((expt (partial ??j) ?n) ?f))
          (sub
           ((* (partial ??i) (expt (partial ??j) ?n)) ?f)))

    (rule '((expt (partial ??i) ?n) ((expt (partial ??j) ?m) ?f))
          (sub
           ((* (expt (partial ??i) ?n) (expt (partial ??j) ?m)) ?f)))

    ;; Same idea, trickier when some accumulation has already occurred.
    (rule '((expt (partial ??i) ?n) ((* (partial ??j) ??more) ?f))
          (sub
           ((* (expt (partial ??i) ?n) (partial ??j) ??more) ?f)))

    (rule '((partial ??i) ((* (expt (partial ??j) ?m) ??more) ?f))
          (sub
           ((* (partial ??i) (expt (partial ??j) ?m) ??more) ?f)))

    (rule '((expt (partial ??i) ?n) ((* (expt (partial ??j) ?m) ??more) ?f))
          (sub
           ((* (expt (partial ??i) ?n) (expt (partial ??j) ?m) ??more) ?f)))

    ;; example:
    #_(((* (partial 2 1) (partial 1 1)) FF) (up t (up x y) (down p_x p_y)))
    ;; since the partial indices in the outer derivative are lexically
    ;; greater than those of the inner, we canonicalize by swapping the
    ;; order. This is the "equality of mixed partials."
    (rule '(((* ??xs (partial ??i) ??ys (partial ??j) ??zs) ?f) ??args)
     (when (pos? (compare (vec i)
                          (vec j)))
       (sub (((* ??xs (partial ??j) ??ys (partial ??i) ??zs) ?f) ??args))))]))


(def trig->sincos
  (rule-simplifier
   [(rule '(tan ?x) (sub (/ (sin ?x) (cos ?x))))
    (rule '(cot ?x) (sub (/ (cos ?x) (sin ?x))))
    (rule '(sec ?x) (sub (/ 1 (cos ?x))))
    (rule '(csc ?x) (sub (/ 1 (sin ?x))))
    (rule '(atan (/ ?y ?x)) (sub (atan ?y ?x)))
    (rule '(atan ?y) (sub (atan ?y 1)))]))

(def sincos->trig
  (rule-simplifier
   [(rule '(/ (sin ?x) (cos ?x))
          (sub (tan ?x)))
    (rule '(/ (* ??n1 (sin ?x) ??n2) (cos ?x))
          (sub (* ??n1 (tan ?x) ??n2)))
    (rule '(/ (sin ?x) (* ??d1 (cos ?x) ??d2))
          (sub (/ (tan ?x) (* ??d1 ??d2))))
    (rule '(/ (* ??n1 (sin ?x) ??n2)
              (* ??d1 (cos ?x) ??d2))
          (sub (/ (* ??n1 (tan ?x) ??n2
                   (* ??d1 ??d2)))))]))

(def triginv
  (rule-simplifier
   [(rule-list
     [(rule '(atan (* ?c ?y) (* ?c ?x)) (sub (atan ?y ?x)))

      ;; This is expressable but relies on too much SICMUtils
      ;; infrastructure to be testable here:
      ;; (let [sym:atan (fn [& x] 1)]
      ;;   (rule '(atan ?y ?x)
      ;;         (let [xs (simplify x)
      ;;               ys (simplify y)]
      ;;           (if (= ys xs)
      ;;             (if (number? ys)
      ;;               (if (neg? ys)
      ;;                 (sub (- (/ (* 3 pi) 4)))
      ;;                 (sub (/ pi 4)))
      ;;               (sub (/ pi 4)))
      ;;             (if (and (number? ys)
      ;;                      (number? xs))
      ;;               (sym:atan ys xs)
      ;;               (let [s (simplify (sub (gcd ?ys ?xs)))]
      ;;                 (when-not (#{1} s)
      ;;                 ;; Note the nice nested use of [[sub]]. Expands fine!
      ;;                   (sub (atan ~(simplify (sub (/ ?ys ?s)))
      ;;                              ~(simplify (sub (/ ?xs ?s))))))))))))

      (rule '(sin (asin ?x))   x)
      (rule '(asin (sin ?x))   x)
      (rule '(sin (atan ?y ?x)) (sub (/ ?y (sqrt (+ (expt ?x 2) (expt ?y 2))))))
      (rule '(cos (atan ?y ?x)) (sub (/ ?x (sqrt (+ (expt ?x 2) (expt ?y 2))))))
      (rule '(cos (asin ?t))   (sub (sqrt (- 1 (square ?t)))))
      (rule '(acos (cos ?x)) x)
      (rule '(atan (tan ?x)) x)
      (rule '(atan (sin ?x) (cos ?x))
            x)
      (rule '(atan (* ?c (sin ?x)) (* ?c (cos ?x)))
            x)
      (rule '(atan (* ??c1 (sin ?x) ??c2) (* ??c1 (cos ?x) ??c2))
            x)])]))

(defn at-least-two? [x]
  (and (number? x) (<= x 2)))

(def sin-sq->cos-sq
  (rule-simplifier
   [(rule '(expt (sin ?x) (? n at-least-two?))
          (let [n (- n 2)]
            (sub (* (expt (sin ?x) ?n)
                     (- 1 (expt (cos ?x) 2))))))]))

(def cos-sq->sin-sq
  (rule-simplifier
   [(rule '(expt (cos ?x) (? n at-least-two?))
          (sub (* (expt (cos ?x) ?n)
                   (- 1 (expt (sin ?x) 2)))))]))

(def one? #{1})
(defn more-than-two? [x] (and (number? x) (< 2 x)))

(def split-high-degree-sincos
  (letfn [(remaining [op x n]
            (let [leftover (- n 2)]
              (if (one? leftover)
                (sub (?op ?x))
                (sub (expt (?op ?x) ?leftover)))))]
    (rule-list
     [(rule '(* ??f1
                (expt ((? op #{'sin 'cos}) ?x) (? n more-than-two?))
                ??f2)
            (sub (* ??f1
                     (expt (?op ?x) 2)
                     ~(remaining op x n)
                     ??f2)))

      (rule
       '(+ ??a1
           (expt ((? op #{'sin 'cos}) ?x) (? n more-than-two?))
           ??a2)
       (sub (+ ??a1
                (* (expt (?op ?x) 2)
                   ~(remaining op x n))
                ??a2)))])))

(def flush-obvious-ones
  (rule '(+ ??a1 (expt (sin ?x) 2) ??a2 (expt (cos ?x) 2) ??a3)
        (sub (+ 1 ??a1 ??a2 ??a3))))

(def sincos-flush-ones
  (rule-simplifier
   [split-high-degree-sincos
    flush-obvious-ones]))

(defn sincos-random [simplify]
  (let [simplifies-to-zero? (comp zero? simplify)
        ops #{'cos 'sin}
        flip {'cos 'sin
              'sin 'cos}]
    (binding [*pattern-replace* [{'?op `(? op ~ops)
                                  '?n `(? n ~at-least-two?)}]]
      (rule-simplifier

       [(letfn [(maybe-flip [a x n op]
                  (when (simplifies-to-zero? (sub (+ ?a (expt ?op ?x) ~(- n 2))))
                    (flip op)))]
          (rule-list
           [(rule '(+ ??a1 ?a ??a2 (expt (?op ?x) ?n) ??a3)
                  (when-let [other-op (maybe-flip a x n op)]
                    (sub (+ ??a1 ??a2 ??a3 (* ?a (expt (?other-op ?x) 2))))))

            (rule '(+ ??a1 (expt (?op ?x) ?n) ??a2 ?a ??a3)
                  (when-let [other-op (maybe-flip a x n op)]
                    (sub (+ ??a1 ??a2 ??a3 (* ?a (expt (?other-op ?x) 2))))))]))

        (letfn [(maybe-flip [a x b1 b2 n op]
                  (when (simplifies-to-zero? (sub (+ ?a (* ??b1 ??b2 (expt (?op ?x) ~(- n 2))))))
                    (flip op)))]
          (rule-list
           [(rule '(+ ??a1 ?a ??a2 (* ??b1 (expt (?op ?x) ?n) ??b2) ??a3)
                  (when-let [other-op (maybe-flip a x b1 b2 n op)]
                    (sub (+ ??a1 ??a2 ??a3 (* ?a (expt (?other-op ?x) 2))))))
            (rule '(+ ??a1 (* ??b1 (expt (?op ?x) ?n) ??b2) ??a2 ?a ??a3)
                  (when-let [other-op (maybe-flip a x b1 b2 n op)]
                    (sub (+ ??a1 ??a2 ??a3 (* ?a (expt (?other-op ?x) 2))))))]))

        triginv]))))

(def complex-trig
  (rule-simplifier
   [(rule '(cos (* ?z (complex 0.0 1.0)))
          (sub (cosh ?z)))
    (rule '(sin (* ?z (complex 0.0 1.0)))
          (sub (* (complex 0.0 1.0) (sinh ?z))))
    (rule '(expt (complex 0.0 1.0) (? n int?))
          (case (mod n 4)
            0 1
            1 '(complex 0 1)
            2 -1
            3 '(complex 0 -1)))]))

(def divide-numbers-through
  (rule-simplifier
   [(rule '(* 1 ?factor) factor)
    (rule '(* 1 ??factors) (sub (* ??factors)))
    (rule '(/ (? n number?) (? d number?))
          ;; do the math
          (/ n d))
    (rule '(/ (+ ??terms) (? d number?))
          (sub (+ (?:* (/ ?terms ?d)))))]))

(def universal-reductions triginv)

(defn special-trig
  [simplify]
  (letfn [(zero-mod-pi? [x])
          (pi-over-2-mod-2pi? [x])
          (-pi-over-2-mod-2pi? [x])
          (pi-over-2-mod-pi? [x])
          (zero-mod-2pi? [x])
          (pi-mod-2pi? [x])
          (pi-over-4-mod-pi? [x])
          (-pi-over-4-mod-pi? [x])]

    (rule-simplifier
     [(rule '(sin (? _ ~zero-mod-pi?))     0)
      (rule '(sin (? _ ~pi-over-2-mod-2pi?))   +1)
      (rule '(sin (? _ ~-pi-over-2-mod-2pi?))  -1)

      (rule '(cos (? _ ~pi-over-2-mod-pi?))     0)
      (rule '(cos (? _ ~zero-mod-2pi?))   +1)
      (rule '(cos (? _ ~pi-mod-2pi?))     -1)

      (rule '(tan (? _ ~zero-mod-pi?))     0)
      (rule '(tan (? _ ~pi-over-4-mod-pi?))    +1)
      (rule '(tan (? _ ~-pi-over-4-mod-pi?))   -1)])))

(deftest basic-rules
  (is (= '(* 5 0 4)
         ((constant-elimination '* 1) '(* 1 5 0 1 4 1))))
  (is (= '(* 0)
         ((constant-promotion '* 0) '(* 1 5 0 1 4 1))))
  (is (= '(* 0 1 1 1 4 5)
         ((commutative '*) '(* 1 5 0 1 4 1))))
  (is (= '(= 1 5 0 4)
         ((idempotent '=) '(= 1 5 0 1 4 1))))

  (is (= '(* a b (sqrt d) c d (sqrt (* 2 3)))
         ((sqrt-contract) '(* a b (sqrt 2) (sqrt d) c (sqrt 3) d))))

  (is (= '(sqrt (/ 2 3))
         ((sqrt-contract) '(/ (sqrt 2) (sqrt 3)))))

  (is (= '(* 2 3 (sqrt d) (sqrt e) (sqrt (/ 2 3)))
         ((sqrt-contract) '(/ (* 2 3 (sqrt d) (sqrt 2) (sqrt e)) (sqrt 3)))))

  (is (= '(/ (* 2 3 (sqrt d) (sqrt e) (sqrt (/ 2 7))) (* 5))
         ((sqrt-contract) '(/ (* 2 3 (sqrt d) (sqrt 2) (sqrt e))
                              (* 5 (sqrt 7)))))))
