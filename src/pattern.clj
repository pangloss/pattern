(ns pattern
  (:require pattern.match.core
            pattern.matchers
            pattern.substitute
            pattern.r3.core
            pattern.r3.rule
            pattern.r3.scanner
            pattern.r3.post-process
            pattern.r3.combinators
            pattern.r3.rewrite
            pattern.matchers.set
            pattern.matchers.map
            pattern.nanopass.dialect
            pattern.nanopass.pass
            pattern.match.predicator
            pattern.types
            pattern.util
            [potemkin :refer [import-vars]]))

(import-vars (pattern.match.core
              matcher
              compile-pattern
              pattern-names
              match?)
             (pattern.util
              listy?)
             (pattern.substitute
              substitute)
             (pattern.r3.rewrite
              sub
              sub+
              subm
              subm+
              rmeta
              quo
              spliced
              eval-spliced
              with-env-args)
             (pattern.r3.core
              rule
              success
              success:env
              name-rule
              rebuild-rule)
             (pattern.r3.rule
               rule-name)
             (pattern.r3.post-process
              use-post-processors
              use-post-processor
              post-processors
              ;; post processors:
              mark-success
              merge-metadata
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
              prewalk-simplifier
              directed
              on-mutual
              rule-simplifier
              in
              rule-zipper)
             (pattern.r3.scanner
               scanner)
             (pattern.nanopass.dialect
              def-dialect
              def-derived
              => ==> ===>
              from-dialect to-dialect dialects
              show-dialect
              show-parse
              valid? validate
              descend-into)
             (pattern.types
               ok ok?
               spliceable-pattern
               recombine)
             (pattern.nanopass.pass
              defpass
              let-rulefn)
             (pattern.match.predicator
               with-predicates))
