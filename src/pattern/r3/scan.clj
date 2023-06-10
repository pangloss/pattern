(ns pattern.r3.scan
  (:require [pattern.r3.core :refer [rule name-rule rule-fn-body pattern-args raw-matches success]]
            [pattern.r3.rewrite :refer [sub spliced]]
            [pattern.r3.combinators :refer [in-order iterated]]
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
         "
  [name pattern body]
  (when-not (:no-assert (meta pattern))
    (assert (matcher ''[??_] pattern) "Pattern must be a vector"))
  (let [result (gensym 'result) ?result  (symbol (str "?" result))
        before (gensym 'before) ??before (symbol (str "??" before))
        after  (gensym 'after)  ??after  (symbol (str "??" after))
        full-pattern (sub '[~?result [~??before ~@(second pattern) ~??after]])
        full-handler (if (:rescan (meta pattern))
                       `(let [changed# ~body]
                          [(into ~result ~before)
                           (into (vec changed#) ~after)])
                       `(let [changed# ~body]
                          [(into ~result (concat ~before changed#))
                           ~after]))]
    `(in-order
       (raw
         (rule ~(symbol (str "PRE-" name))
           '~'(? v sequential?)
           (success [[] (vec ~'v)])))
       (iterated
         (name-rule '~name
           (let [p# ~(spliced full-pattern)]
             (make-rule p#
               (rule-fn-body ~name
                 ~(pattern-args full-pattern)
                 ~(:env-args (meta pattern))
                 ~full-handler)
               raw-matches
               *post-processor*
               {:may-call-success0? false
                :src '~full-handler
                :pattern-meta '~(meta pattern)}))))
       (raw
         (rule ~(symbol (str "POST-" name))
           '~'[?result ?remainder]
           (into ~'result ~'remainder))))))



(comment
  (def e1
    (scan-rule minimal-example
      '[?a ?a]
      [a]))

  (e1 [1 2 2 3 3 3 4 4 4 4])
  ;; => [1 2 3 3 4 4]


  ((scan-rule minimal-example ^:rescan
     '[?a ?a]
     [a])
   [1 2 2 3 3 3 4 4 4 4])
  ;; => [1 2 3 4]

  ((iterated
     (rule basic-example
       '[??before ?a ?a ??after]
       (sub [??before ?a ??after])))
   [1 2 2 3 3 3 4 4 4 4])
  ;; => [1 2 3 4]



  (scan-rule combine
    '[(?:as* coll
        (?:1
          (?:map :pos ?pos)
          (?:* (?:map :pos (| ?pos :ws)))
          (?:map :pos ?pos)))]
    [{:text (clojure.string/join (map :text coll)) :pos pos}]))
