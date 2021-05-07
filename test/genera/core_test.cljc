(ns genera.core-test
  (:require [clojure.test :refer :all]
            [genera.core :refer :all]))

(comment
  (def add (simple-generic-procedure 'add 2 +))
  (assign-handler! add list odd? odd?)
  (assign-handler! add / int? even?) ;; mathematically sound
  (assign-handler! add * odd? even?) ;; mathematically sound
  (add 3 5)
  (add 5 4)
  (add 4 5))
