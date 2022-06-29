(ns compiler-course.pass14-remove-jumps
  (:require
   [compiler-course.dialects :refer :all]
   [pattern :refer [=> dialects directed rule rule-list sub success]]))


;; Combine blocks when a jump is not needed

(def remove-jumps
  (dialects
   (=> RemoveUnallocated RemoveUnallocated)
   (directed (rule-list (rule '(program ??->define*))
                        (rule '(define ?d ?vars ?var-locs [(& ?blocks ?->jumps) ...])
                              (let [blocks (reduce (fn [m [_ label :as b]]
                                                     (assoc m label b))
                                                   {} blocks)
                                    linear-jumps
                                    (->> (group-by second jumps)
                                         (filter #(= 1 (count (val %))))
                                         vals
                                         (apply concat)
                                         (into {}))
                                    blocks
                                    (reduce-kv (fn [blocks from to]
                                                 (let [from (loop [b (blocks from)]
                                                              (if (symbol? b)
                                                                (recur (blocks b))
                                                                (:label b)))]
                                                   (if (and (blocks from) (blocks to))
                                                     (-> blocks
                                                         (update from (fn [b]
                                                                        (sub (~@(butlast b)
                                                                              ~@(drop 3 (blocks to))))))
                                                         (assoc to from))
                                                     blocks)))
                                               blocks linear-jumps)]
                                (sub (define ?d ?vars ?var-locs [~@(remove symbol? (vals blocks))]))))
                        (rule '(block ?from ??stmt* (jump ?jc ?to))
                              [from to])
                        (rule '(block ??any)
                              (success nil))))))
