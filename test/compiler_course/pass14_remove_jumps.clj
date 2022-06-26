(ns compiler-course.pass14-remove-jumps
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  caller-saved-registers callee-saved-registers
                                                  var-locations with-allocated-registers]]
            [compiler-course.dialects :refer [r1-keyword?]]
            [matches.nanopass.dialect :refer [all-dialects =>:to show-parse]]
            [matches :refer [descend in gennice niceid directed on-subexpressions rule rule-list rule-list!
                             descend-all sub success subm rule-simplifier matcher
                             => dialects validate ok ok?]]
            [matches.types :refer [child-rules]]
            [clojure.string :as str]))


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
