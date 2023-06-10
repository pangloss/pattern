(ns pattern.r3.scan
  (:require [pattern.r3.core :refer [rule name-rule rule-fn-body pattern-args raw-matches success]]
            [pattern.r3.rewrite :refer [sub spliced]]
            [pattern.r3.combinators :refer [in-order iterated guard]]
            [pattern.r3.rule :refer [make-rule *post-processor*]]
            [pattern.r3.post-process :refer [raw]]
            [pattern.match.core :refer [matcher]]))

(defmacro scan-rule
  "Create a specialized rule variant that scans through a collection and
  replaces matching sequences with new sequences.

  The pattern must be a vector, which may match any number of items. The

  This example matches exactly 2 identical items and replaces them with one:

         ((scan-rule minimal-example
            '[?a ?a]
            [a])
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 3 4 4]

  The result is not rescanned, resulting in 3 to appear twice after matching
  since the third appearance is solo after the first pair has been transformed.

  To enable result rescanning, add ^:rescan before the pattern:

         ((scan-rule minimal-example ^:rescan
            '[?a ?a]
            [a])
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 4]

  The rule moves monotonically forward through the list without
  rescanning of the previously matched list that typically happens with a
  simpler rule such as the following:

         ((iterated
            (rule basic-example
              '[??before ?a ?a ??after]
              (sub [??before ?a ??after])))
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 4]

  For lists under about 10 elements, the above naive strategy seems a little
  faster. If you enable ^:rescan, lists under length 10 will use the naive strategy. You can change the
  threshold number from 10 to any n you as follows:

         (scan-rule x ^{:rescan true :optimize-at-count n} '[?a ?a] [a])

  Setting :optimize-at-count to 0 will cause all lengths to use the optimized
  strategy, or setting it to Long/MAX_VALUE will force all lengths to use the
  naive strategy."
  [name pattern body]
  (when-not (:no-assert (meta pattern))
    (assert (matcher ''[??_] pattern) "Pattern must be a vector"))
  (let [result  (gensym 'result)  ?result   (symbol (str "?"  result))
        before  (gensym 'before)  ??before  (symbol (str "??" before))
        after   (gensym 'after)   ??after   (symbol (str "??" after))
        changed (gensym 'changed) ??changed (symbol (str "??" changed))
        remove-quote second ;; second element in (quote x) is the element itself.
        full-pattern (sub '[~?result [~??before ~@(remove-quote pattern) ~??after]])
        rescan? (:rescan (meta pattern))
        full-handler (if rescan?
                       `(let [changed# ~body]
                          [(into ~result ~before)
                           (into (vec changed#) ~after)])
                       `(let [changed# ~body]
                          [(into ~result (concat ~before changed#))
                           ~after]))
        small-pattern (when rescan?
                        (sub '[~??before ~@(remove-quote pattern) ~??after]))
        small-handler (when rescan?
                        `(let [~changed ~body]
                           (sub [~??before ~??changed ~??after])))
        ;; number of elements that we start using the optimized strategy
        optimize-at-count (if rescan? (:optimize-at-count (meta pattern) 10) 0)]
    `(in-order
       (raw
         (rule ~(symbol (str "PRE-" name))
           '~'(? v sequential?)
           (let [v# (vec ~'v)]
             (if (< (count v#) ~optimize-at-count)
               v#
               (success [[] (vec ~'v)] (assoc ~'%env ::long true))))))
       (guard (fn [_# env#] (::long env#))
         (in-order
           (iterated
             (name-rule '~name
               (make-rule ~(spliced full-pattern)
                 (rule-fn-body ~name
                   ~(pattern-args full-pattern)
                   ~(:env-args (meta pattern))
                   ~full-handler)
                 raw-matches
                 *post-processor*
                 {:may-call-success0? false
                  :src '~full-handler
                  :pattern-meta '~(meta pattern)})))
           (raw
             (rule ~(symbol (str "POST-" name))
               '~'[?result ?remainder]
               (if (seq ~'result)
                 (if (seq ~'remainder)
                   (into ~'result ~'remainder)
                   ~'result)
                 ~'remainder)))))
       (guard (fn [_# env#] (not (:long env#)))
         (iterated
           (name-rule '~(symbol (str "SMALL-" name))
             (make-rule ~(spliced small-pattern)
               (rule-fn-body ~name
                 ~(pattern-args small-pattern)
                 ~(:env-args (meta pattern))
                 ~small-handler)
               raw-matches
               *post-processor*
               {:may-call-success0? false
                :src '~small-handler
                :pattern-meta '~(meta pattern)})))))))

(comment
  (def e1
    (scan-rule minimal-example ^:rescan
      '[?a ?a]
      [a]))

  (e1 [1 4 4 4 4])

  ;; => [1 2 3 3 4 4]


  (let [orig (iterated
               (rule basic-example
                 '[??before ?a ?a ??after]
                 (sub [??before ?a ??after])))
        fast (scan-rule minimal-example ^{:rescan true :optimize-at-count 0}
               '[?a ?a]
               [a])]

    (for [n (range 0 100 2)
          :let [data (vec (take n (cycle [1 2 2 3 3 3 4 4 4 4 5 5 5 5 5 6 6 6 6 6 6 7 7 7 7 7 7 7 8 8 8 8 8 8 8 8])))]]
      (do
        (println (count data))
        (println
          (=
            (time
              (do (print "fast? ")
                  (vec
                    (for [_ (range 1000)]
                      (fast data)))))
            (time
              (do (print "orig: ")
                  (vec
                    (for [_ (range 1000)]
                      (orig data))))))))))



  (scan-rule combine
    '[(?:as* coll
        (?:1
          (?:map :pos ?pos)
          (?:* (?:map :pos (| ?pos :ws)))
          (?:map :pos ?pos)))]
    [{:text (clojure.string/join (map :text coll)) :pos pos}]))
