(ns sub-test
  (:require [clojure.test :refer :all]
            [pattern.substitute :refer [substitute]]
            [pattern.match.core :refer [matcher var-name *disable-modes*]]
            [pure-conditioning :as c :refer [manage restart-with handler-cond]]
            [clojure.test :as t]))


(deftest sub-optional
  (is (= [0 123 [123] 1 2]
         (substitute '[0 (?:? ?y [?y]) 1 2] {'y 123})))
  (is (= '(0 123 (0 1 (0 1 123)) 1 2)
         (substitute '(0 (?:? ?y (0 1 (0 1 ?y))) 1 2) {'y 123})))
  (is (= [0 123 123 1 2]
         (substitute '[0 (?:? ?x ?x) 1 2] {'x 123})))
  (is (= [0 1 2]
         (substitute '[0 (?:? ?x ?x) 1 2] {'y 123})))
  (testing "with metadata"
    (let [r (substitute '[0 (?:+ ?y [?y]) 1 ?y] {'y [1 (with-meta 'b {:n 123})]})]
      (is (= [nil nil nil {:n 123} nil nil nil]
             (map meta r))))))


(deftest sub-failure-callback
  ;; This style of failure handling makes a lot more sense. With no context, it seems useless.
  ;; Will the tests pass??
  (testing "Replicate the default behaviour of leaving the pattern in place if it does not match"
    (is (= '[(?:+ ?a ?a ?x) ?b ?c]
           ((substitute '((?:+ ?a ?a ?x) ?b ?c))
            {}
            (fn [d n p] [p])))))

  (testing "replace missing pattern with pattern name"
    (is (= '[nil b c]
           ((substitute '((?:+ ?a ?a ?x) ?b ?c))
            {}
            (fn [d n p] [n])))))

  (testing "omit non-matching elements"
    (is (= '[]
           ((substitute '((?:+ ?a ?a ?x) ?b ?c))
            {}
            (fn [d n p] [])))))

  (testing "example of doing something vaguely interesting on failure"
    (is (= '[?a ?a ?x ?b ?c]
           ((substitute '((?:+ ?a ?a ?x) ?b ?c))
            {}
            (fn [d n p]
              (if (nil? n)
                (rest p)
                [p])))))))


(deftest sub-conditional
  (is (= [1 2]
         (substitute '[(?:? ?a ?b)] {'a 1 'b 2})))
  (is (= '[x]
         (substitute '[(?:if symbol? ?a ?b)] {'a 'x 'b 999})))
  (is (= '[x]
         (substitute '[(?:if symbol? ?b ?a)] {'a 'x 'b 999})))
  (is (= '[(?:when symbol? ?a ?none)]
         (substitute '[(?:when symbol? ?a ?none)] {'a 'x 'b 999})))
  (is (= '[x 999]
         (substitute '[(?:when symbol? ?a ?b)] {'a 'x 'b 999})))
  (is (= []
         (substitute '[(?:when symbol? ?b ?a)] {'a 'x 'b 999}))))

(deftest sub-map-variants
  (testing "map"
    (is (= [{1 2}]
          (substitute ['(?:map ?a ?b)] {'a 1 'b 2})))
    (is (= ['(?:map ?a ?b)]
          (substitute ['(?:map ?a ?b)] {'a 1})))
    (is (= ['(?:map ?a ?b)]
          (substitute ['(?:map ?a ?b)] {'b 2})))
    (is (= [{1 2 2 1}]
          (substitute ['(?:map ?a ?b ?b ?a)] {'a 1 'b 2}))))
  (testing "*map"
    (is (= ['(?:*map ?a ?b)]
          (substitute ['(?:*map ?a ?b)] {'a 1 'b 2})))
    (is (= [{1 2}]
          (substitute ['(?:*map ?a ?b)] {'a [1] 'b [2]})))
    (is (= [{1 2 3 4}]
          (substitute ['(?:*map ?a ?b)] {'a [1 3] 'b [2 4]})))
    (is (= ['(?:*map ?a ?b)]
          (substitute ['(?:*map ?a ?b)] {'a [1] 'b 2})))
    (is (= ['(?:map* ?a ?b)]
          (substitute ['(?:map* ?a ?b)] {'a 1 'b [2]}))))
  (testing "set"
    (is (= [#{1 2 3}]
          (substitute ['(?:set ?x)] {'x [1 2 3]})))
    (is (= [#{1 2 3}]
          (substitute ['(?:set ?x)] {'x [1 2 3 3]})))
    (is (= ['(?:set ?x)]
          (substitute ['(?:set ?x)] {'x 1}))))
  (testing "as"
    (is (= [1]
          (substitute ['(?:as x ?z)] {'x 1 'z 2})))
    (is (= [2]
          (substitute ['(?:as x ?z)] {'y 1 'z 2})))
    (is (= ['[?a 1]]
          (substitute ['(?:as x [?a ?z])] {'z 1})))
    (is (= ['(?:as x [?a ?z])]
          (substitute ['(?:as x [?a ?z])] {}))))
  (testing "as*"
    (is (= [1 2]
          (substitute ['(?:as* x ?z)] {'x [1 2] 'z [3 4]})))
    (is (= [[3 4]]
          (substitute ['(?:as* x ?z)] {'y [1 2] 'z [3 4]})))
    (is (= [3 4]
          (substitute ['(?:as* x ??z)] {'y [1 2] 'z [3 4]})))
    (is (= [] ;; no match on optional matcher.
          (substitute ['(?:as* x (?:? ?a ?z))] {'z 1})))
    (is (= [] ;; optional is successful with 0 matches.
          (substitute ['(?:as* x (?:? ?a ?z))] {})))
    (is (= ['(?:as* x (?:1 ?a ?z))] ;; optional is successful with 0 matches.
          (substitute ['(?:as* x (?:1 ?a ?z))] {})))
    (is (= ['(?:as* x [?a ?z])]
          (substitute ['(?:as* x [?a ?z])] {}))))
  (testing "wrong arities"
    (is (thrown-with-msg? Exception #"Invalid zipmap pattern.*"
          (substitute ['(?:*map ?a)] {'a [1]})))
    (is (thrown-with-msg? Exception #"Invalid zipmap pattern.*"
          (substitute ['(?:*map)] {'a [1]})))
    (is (thrown-with-msg? Exception #"Invalid zipmap pattern.*"
          (substitute ['(?:*map ?a ?b ?c)] {'a [1] 'b [2]})))
    (is (thrown-with-msg? Exception #"Invalid map pattern.*"
          (substitute ['(?:map ?a)] {'a 1})))))


(deftest sub-one-splice
  (is (= [99 1]
        (substitute ['(?:1 ?a ?z)] {'z 1 'a 99})))
  (is (= ['?a 1]
        (substitute ['(?:1 ?a ?z)] {'z 1})))
  (is (= ['(?:1 ?a ?z)]
        (substitute ['(?:1 ?a ?z)] {}))))

(deftest sub-multi-recursive
  (testing "with regular quote"
    (is (= '[[[0 1] <> 0 <> 1] [[2 3] <> 2 <> 3]]
           (substitute '[(?:* [?x (?:* <> ?x)])] {'x [[0 1] [2 3]]})))
    (is (= '[<> 0 hi <> 1 hi <> 2 hi <> 3 hi]
           (substitute '[(?:* (?:* <> ?x ?y))] {'x [[0 1] [2 3]] 'y 'hi}))))

  (testing "with syntax quote"
    (is (= `[[[0 1] <> 0 <> 1] [[2 3] <> 2 <> 3]]
           (substitute `[(?:* [?x (?:* <> ?x)])] {'x [[0 1] [2 3]]})))
    (is (= '[<> 0 hi <> 1 hi <> 2 hi <> 3 hi]
           (substitute '[(?:* (?:* <> ?x ?y))] {'x [[0 1] [2 3]] 'y 'hi}))))

  (testing "nanopass example (both quoting styles)"
    ;; nanopass example
    (is (= `(begin (set! a 1) (set! b 2) (set! c 3) (...) ...)
           (substitute `(begin (?:* (set! ?x ?e)) ??body)
                       {'x `[a b c] 'e [1 2 3] 'body `[(...) ...]})))
    (is (= '(begin (set! a 1) (set! b 2) (set! c 3) (...) ...)
           (substitute '(begin (?:* (set! ?x ?e)) ??body)
                       '{x [a b c] e [1 2 3] body [(...) ...]})))))


(deftest match-on-subbed-list
  (is (= '(sequence-matching 123)
         (-> '(set! ?v ?i)
             (substitute '{v (? v symbol?) i (? i int?)})
             (matcher '(set! sequence-matching 123)))))
  (is (= nil
         (-> '(set! ?v ?i)
             (substitute '{v (? v symbol?) i (? i int?)})
             (matcher '(set! sequence-matching 1.23))))))
