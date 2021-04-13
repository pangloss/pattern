(ns matches
  (:require matches.matchers
            matches.substitute
            matches.rules
            matches.rewrite
            [potemkin :refer [import-vars]]))

(import-vars (matches.match.core matcher pattern-names)
             (matches.substitute substitute)
             (matches.rewrite sub quo spliced eval-spliced)
             (matches.rules rule rule-fn success rule-name)
             (matches.rule-combinators rule-list
                                       in-order
                                       descend
                                       on-subexpressions
                                       iterated-on-subexpressions
                                       directed
                                       on-mutual
                                       rule-simplifier))
