(ns pattern
  (:require pattern.matchers
            pattern.substitute
            pattern.r3.core
            pattern.r3.combinators
            pattern.r3.rewrite
            pattern.nanopass.dialect
            pattern.nanopass.pass
            pattern.types
            [potemkin :refer [import-vars]]))

(import-vars (pattern.match.core
              matcher
              compile-pattern
              pattern-names)
             (pattern.substitute
              substitute)
             (pattern.r3.rewrite
              sub
              subm
              subm!
              rmeta
              quo
              spliced
              eval-spliced
              with-env-args)
             (pattern.r3.core
              rule
              success
              success:env
              rule-name)
             (pattern.r3.combinators
              rule-list
              rule-list!
              in-order
              descend
              descend-all
              on-subexpressions
              simplifier
              directed
              on-mutual
              rule-simplifier
              in gennice niceid)
             (pattern.nanopass.dialect
              def-dialect
              def-derived
              => ==> ===>
              from-dialect to-dialect dialects
              show-dialect
              show-parse
              valid? validate)
             (pattern.types ok ok?)
             (pattern.nanopass.pass
              defpass
              let-rulefn))
