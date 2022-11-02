(ns demo.infix
  (:require [pattern :refer :all]
            [simplify-test :refer [expr<?]]
            [pattern.match.predicator :refer [*pattern-replace* make-abbr-predicator]]))

(defmacro with-predicates [rule]
  (sub
    (binding [*pattern-replace*
              [(make-abbr-predicator 'x number?)
               (make-abbr-predicator 'y number?)
               (make-abbr-predicator 'comm #{'+ '*})]]
      ?rule)))

(def explicit-operator-precedence
  (with-predicates
    (rule-list
      (rule group-division
        '(??a* ?a / ?b ??b*)
        (when (or (seq a*) (seq b*))
          (sub (??a* (?a / ?b) ??b*))))

      (rule group-multiplication
        '(??a* ?a (?:+ * ?b) ??b*)
        (if (or (and (seq a*)
                  (not= '* (last a*)))
              (and (seq b*)
                (not= '* (first b*))))
          (sub (??a* (?a (?:+ * ?b)) ??b*)))))))

(def sort-commutative-operations
  (with-predicates
    (rule sort-comm
      '(??a* ?b ?comm ?a ??b*)
      (when (expr<? a b)
        (sub (??a* ?a ?comm ?b ??b*))))))

(def division-rules
  (with-predicates
    (rule-list
      (rule div-zero
        '(?a / 0)
        (sub (?a / 0)))

      (rule div-id
        '(?a / 1)
        a)

      (rule apply-div
        '(?x / ?y)
        (/ x y))

      (rule self-div
        '(?a / ?a)
        1))))

(def multiply-rules
  (with-predicates
    (rule-list
      (rule apply-*
        '(??a ?x (?:+ * ?y) ??b)
        (sub (??a ~(apply * x y) ??b)))

      (rule mult-id
        '(1 * ?a)
        a)

      (rule mult-zero
        '(0 * ?a)
        0))))

(def apply-add-sub
  (with-predicates
    (simplifier
      (rule-list
        (rule add-id
          '(0 + ?a)
          a)

        (rule apply-add
          '(??a ?x + ?y ??b)
          (sub (??a ~(+ x y) ??b)))

        (rule apply-sub
          '(??a ?x - ?y ??b)
          (sub (??a ~(- x y) ??b)))))))


(def math
  (with-predicates
    (simplifier
      (rule-list
        explicit-operator-precedence
        sort-commutative-operations
        multiply-rules
        division-rules
        apply-add-sub
        (rule ungroup-solo
          '(?a)
          a)))))

(math '(3 / 9 * 2))
(math '(3 / 9 * 0))
(math '(3 / (9 * 0)))
(math '(3 / 0))
(math '(a * b * c * a * 1 * 2 * 3))
(math '(a * b + c * a * 1 * 2 * 3))
(math '(3 + v / (1 * v) + 3 * 4 * 5 * 6 + (x * 0)))
