(ns pattern
  (:require pattern.matchers
            pattern.match.core
            pattern.substitute
            pattern.r3.core
            pattern.r3.rule
            pattern.r3.post-process
            pattern.r3.combinators
            pattern.r3.rewrite
            pattern.nanopass.dialect
            pattern.nanopass.pass
            pattern.types
            [potemkin :refer [import-vars]]))

(import-vars (pattern.match.core
              matcher
              compile-pattern
              pattern-names
              listy?)
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
              name-rule)
             (pattern.r3.rule
               rule-name)
             (pattern.r3.post-process
              deep-merge-metadata
              mark-success
              use-post-processors
              use-post-processor
              post-processors
              raw)
             (pattern.r3.combinators
              rule-list
              rule-list!
              in-order
              descend
              descend-all
              on-subexpressions
              iterated
              simplifier
              directed
              on-mutual
              rule-simplifier
              in)
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
