(ns matches
  (:require matches.matchers
            matches.substitute
            matches.r2.core
            matches.r2.combinators
            matches.r2.rewrite
            [potemkin :refer [import-vars]]))

(import-vars (matches.match.core
              matcher
              compile-pattern
              pattern-names)
             (matches.substitute
              substitute)
             (matches.r2.rewrite
              sub
              quo
              spliced
              eval-spliced)
             (matches.r2.core
              rule
              success
              success:env
              rule-name)
             (matches.r2.combinators
              rule-list
              in-order
              descend
              on-subexpressions
              simplifier
              directed
              on-mutual
              rule-simplifier))
