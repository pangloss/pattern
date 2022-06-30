(ns pattern.r3.post-process-test
  (:require [pattern.r3.post-process :as sut]
            [pattern :refer [rule]]
            [clojure.test :refer [deftest testing is]]))


(deftest compose-pp
  (is (= [3 2000]
        ;; I'm not using the args correctly here, just testing the composed behavior.
        ((sut/comp-post-processors
           (fn [_ v ov e oe] [(+ v ov) (* e oe)])
           (fn [_ v ov e oe] [(+ v ov) (* e oe)])
           (fn [_ v ov e oe] [(+ v ov) (* e oe)]))
         nil 0 1 2 10))))


(deftest marking-success
  (is (= [3 {:rule/datum '(+ 1 2)}]
        ((rule '(+ 1 ?x) 3) '(+ 1 2) {})))
  (is (= [3 {:rule/datum '(+ 1 2)}]
        ((rule add1+2 '(+ 1 ?x) 3) '(+ 1 2) {})))

  (sut/use-post-processor sut/mark-success
    (is (= [3 {:rule/datum '(+ 1 2)
               :rule/success ['(+ 1 ?x)]}]
          ((rule '(+ 1 ?x) 3) '(+ 1 2) {})))
    (is (= [3 {:rule/datum '(+ 1 2)
               :rule/success ['add1+2]}]
          ((rule add1+2 '(+ 1 ?x) 3) '(+ 1 2) {}))))

  (is (= [3 {:rule/datum '(+ 1 2)
             :rule/success ['(+ 1 ?x)]}]
        ((sut/with-post-processor sut/mark-success
           (rule '(+ 1 ?x) 3)) '(+ 1 2) {})))
  (is (= [3 {:rule/datum '(+ 1 2)
             :rule/success ['add1+2]}]
        ((sut/with-post-processor sut/mark-success
           (rule add1+2 '(+ 1 ?x) 3)) '(+ 1 2) {})))

  (testing "compose so we mark twice"
    (sut/use-post-processor (sut/comp-post-processors
                              sut/mark-success
                              sut/mark-success)
      (is (= [3 {:rule/datum '(+ 1 2)
                 :rule/success ['(+ 1 ?x)
                                '(+ 1 ?x)]}]
            ((rule '(+ 1 ?x) 3) '(+ 1 2) {})))
      (is (= [3 {:rule/datum '(+ 1 2)
                 :rule/success ['add1+2
                                'add1+2]}]
            ((rule add1+2 '(+ 1 ?x) 3) '(+ 1 2) {}))))))
