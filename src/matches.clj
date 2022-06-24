(ns matches
  (:require matches.matchers
            matches.substitute
            matches.r3.core
            matches.r3.combinators
            matches.r3.rewrite
            matches.nanopass.dialect
            matches.nanopass.pass
            matches.types
            [potemkin :refer [import-vars]]))

(import-vars (matches.match.core
              matcher
              compile-pattern
              pattern-names)
             (matches.substitute
              substitute)
             (matches.r3.rewrite
              sub
              subm
              subm!
              rmeta
              quo
              spliced
              eval-spliced
              with-env-args)
             (matches.r3.core
              rule
              success
              success:env
              rule-name)
             (matches.r3.combinators
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
             (matches.nanopass.dialect
              def-dialect
              def-derived
              => ==> ===>
              from-dialect to-dialect dialects
              show-dialect
              show-parse
              valid? validate)
             (matches.types ok ok?)
             (matches.nanopass.pass
              defpass
              let-rulefn))
