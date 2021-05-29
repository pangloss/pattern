(ns matches
  (:require matches.matchers
            matches.substitute
            matches.r3.core
            matches.r3.combinators
            matches.r3.rewrite
            matches.r3.match
            matches.nanopass.dialect
            matches.nanopass.pass
            [potemkin :refer [import-vars]]))

(import-vars (matches.match.core
              matcher
              compile-pattern
              pattern-names)
             (matches.substitute
              substitute)
             (matches.r3.rewrite
              sub
              quo
              spliced
              eval-spliced)
             (matches.r3.core
              rule
              success
              success:env
              rule-name)
             (matches.r3.match match match!)
             (matches.r3.combinators
              rule-list
              rule-list!
              in-order
              descend
              on-subexpressions
              simplifier
              directed
              on-mutual
              rule-simplifier)
             (matches.nanopass.dialect
              define-dialect
              derive-dialect
              => ==> ===>
              from-dialect to-dialect dialects
              tag-result tag
              unparse-dialect)
             (matches.nanopass.pass
              defpass
              let-rulefn))
