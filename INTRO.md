# Pattern

Pattern is a Clojure library providing a powerful pattern matching and rule-based transformation engine. It supports complex pattern matching with backtracking, predicates, variable binding, and various combinators for building sophisticated matching rules.  Additionally, it includes a "nanopass" framework for defining and applying transformations based on language dialects.

## Core Matching

The fundamental building blocks are `matcher`, `compile-pattern`, and `match?`.

Results of `(matcher pattern input)` and `(match? pattern input)`:
| # | pattern     | input     | matcher result | match? result |
|---|-------------|-----------|----------------|---------------|
| 1 | `'?x`       | `1`       | `(1)`          | `true`        |
| 2 | `1`         | `1`       | `()`           | `true`        |
| 3 | `'(+ ?x ?y)` | `(+ 1 2)` | `(1 2)`        | `true`        |
| 4 | `'(+ ?x ?x)` | `(+ 1 1)` | `(1)`          | `true`        |
| 5 | `'(+ ?x ?x)` | `(+ 1 2)` | `nil`          | `false`       |


Results of `((compile-pattern pattern) input)`:
| #  | pattern     | input     | result       |
|----|-------------|-----------|--------------|
| 6  | `'?x`       | `1`       | `'{x 1}`     |
| 7  | `1`         | `1`       | `{}`         |
| 8  | `'(+ ?x ?y)` | `(+ 1 2)` | `'{x 1 y 2}` |
| 9  | `'(+ ?x ?x)` | `(+ 1 1)` | `'{x 1}`     |
| 10 | `'(+ ?x ?x)` | `(+ 1 2)` | `nil`        |


### `matcher`

Compiles and executes a pattern against a datum. Returns a vector of matched values or `nil` if no match.  The results in the table above represent the result of `(matcher pattern input)`.

```clojure
(let [find-unordered (matcher '(* ?b (? a < ?b)))]
  (find-unordered '(* 1 2))  ;; => nil
  (find-unordered '(* 2 1))) ;; => [2 1]
```

### `compile-pattern`

Compiles a pattern into a reusable function.  Returns a function that takes a datum and returns a map of bindings or `nil`.

```clojure
(let [find-unordered (compile-pattern '(* ?b (? a < ?b)))]
  (find-unordered '(* 1 2))  ;; => nil
  (find-unordered '(* 2 1))) ;; => {'b 2, 'a 1}
```

### `match?`

Similar to `matcher` but returns `true` if the pattern matches and `false` otherwise.

```clojure
(let [is-multiply? (match? '(* ?a ?b))]
  (is-multiply? '(* 1 2)) ;; => true
  (is-multiply? '(+ 1 2))) ;; => false
```


## Pattern Syntax

Patterns are expressed using a combination of literals, variables, and matcher combinators.

* **Literals:**  Match directly against data.  e.g., `1`, `:keyword`, `"string"`.
* **Variables:**  Bind to matched data. Start with `?`. e.g., `?x`, `?name`.  Underscore `?_` acts as a wildcard, matching anything but not binding the result.
* **Matcher Combinators:** Control the matching process.  See below.


## Matcher Combinators

Pattern provides a rich set of matcher combinators for building complex patterns.  They are generally used in list form, starting with a keyword.

| #  | Combinator                                    | Description                                                                                            | Example                            |
|----|-----------------------------------------------|--------------------------------------------------------------------------------------------------------|------------------------------------|
| 11 | `?:=` or `?:literal`                          | Matches a literal value.                                                                               | `(?:= ?x)`                         |
| 12 | `?:list`                                      | Matches a list or vector.                                                                              | `(?:list ?a ?b ?c)`                |
| 13 | `?:seq`                                       | Matches any sequence.                                                                                  | `(?:seq ?a ?b ?c)`                 |
| 14 | `?:?` or `?:optional`                         | Matches a pattern zero or one time.                                                                    | `(?:? ?a)`                         |
| 15 | `?:*` or `?:many`                             | Matches a pattern zero or more times.                                                                  | `(?:* ?a)`                         |
| 16 | `?:+` or `?:at-least-one`                     | Matches a pattern one or more times.                                                                   | `(?:+ ?a)`                         |
| 17 | `?:n`                                         | Matches a pattern a specific number of times.                                                          | `(?:n 2 ?a)`, `(?:n [2 4] ?a)`     |
| 18 | `?:chain`                                     | Applies functions to matched values.                                                                   | `(?:chain ?x meta keys)`           |
| 19 | `?:as`                                        | Captures a sub-pattern's match.                                                                        | `(?:as name [?a ?b])`              |
| 20 | `?:as*`                                       | Always captures as a sequence, even if matching one element.                                           | `(?:as* name [?a ?b])`             |
| 21 | `?:or`                                        | Matches any of the given patterns.                                                                     | `(?:or ?a ?b)`                     |
| 22 | `?:and`                                       | Matches all of the given patterns.                                                                     | `(?:and ?a ?b)`                    |
| 23 | `?:not`                                       | Matches if the given pattern does *not* match.                                                         | `(?:not ?a)`                       |
| 24 | `?:if`                                        | Conditional matching.                                                                                  | `(?:if pred? ?then ?else)`         |
| 25 | `?:when`                                      | Matches multiple patterns if a predicate is true.                                                      | `(?:when pred? ?a ?b)`             |
| 26 | `?:letrec`                                    | Defines named patterns for reuse within a pattern.                                                     | `(?:letrec [pair [?a ?b]] $pair)`  |
| 27 | `?:ref`                                       | References a named pattern defined with `?:letrec`.                                                    | `$A`                               |
| 28 | `?:fresh`                                     | Creates a new scope for variables.                                                                     | `(?:fresh [x] $recursive-pattern)` |
| 29 | `?:all-fresh`                                 | Creates a new scope for all variables within a sub-pattern.                                            | `(?:all-fresh [?x ?y] ...)`        |
| 30 | `?:restartable`                               | Marks a pattern for restartable matching using the `pure-conditioning` library.                        | See examples below.                |
| 31 | `?:re-matches`, `?:re-seq`                    | Match against regular expressions.                                                                     | `(?:re-matches #"pattern" ...)`    |
| 32 | `#{}`, `?:set`, `?:set=`, `??:set`, `??:set=` | Match sets. `?:set=` and `??:set=` match sets exactly.                                                 | `#{?a ?b}`, `(?:set ?a ?b)`        |
| 33 | `?:item`, `??:item`                           | Find the first matching item in a list. Optional second pattern is the remaining elements in the list. | `(?:item ?x ?rest)`                |
| 34 | `{}` `?:map`, `??:map`                        | Match maps or key value pairs. `?:map=` and `??:map=` match maps exactly.                              | `{:a ?x}`, `(?:map :a ?x)`         |
| 35 | `?:nth`, `??:nth`                             | Match the nth element of a sequence.                                                                   | `(?:nth 0 ?x)`                     |


## Extended Examples

The table below demonstrates pattern matching using `matcher`. Each result represents the output of `(matcher pattern input)`.


| #   | pattern                                    | input                             | result            |
|-----|--------------------------------------------|-----------------------------------|-------------------|
| 36  | `'(+ 1 ?x)`                                 | `(+ 1 2)`                         | `(2)`             |
| 37  | `'(+ ?x 1)`                                 | `(+ 2 1)`                         | `(2)`             |
| 38  | `'(+ 1 1)`                                  | `(+ 1 1)`                         | `()`              |
| 39  | `'(+ 1 1)`                                  | `(+ 1 2)`                         | `nil`             |
| 40  | `'(+ ?_ ?y)`                                | `(+ 1 2)`                         | `(2)`             |
| 41  | `'[1 ?x 3]`                                 | `[1 2 3]`                         | `(2)`             |
| 42  | `'[1 ?x ?x]`                                | `[1 2 2]`                         | `(2)`             |
| 43  | `'[1 ?x ?y]`                                | `[1 2 3]`                         | `(2 3)`           |
| 44  | `'(?x ?y)`                                  | `(1 2)`                           | `(1 2)`           |
| 45  | `'[?x ?y]`                                  | `[1 2]`                           | `(1 2)`           |
| 46  | `'(:a ?x :b ?y)`                            | `(:a 1 :b 2)`                     | `(1 2)`           |
| 47  | `'(a ?x b ?y)`                              | `(a 1 b 2)`                       | `(1 2)`           |
| 48  | `'(+ ?x ?y ?z)`                             | `(+ 1 2 3)`                       | `(1 2 3)`         |
| 49  | `'(+ 1 ?x 3)`                               | `(+ 1 2 3)`                       | `(2)`             |
| 50  | `'(+ ?a (?:? ?b))`                          | `(+ 1)`                           | `(1 nil)`         |
| 51  | `'(+ ?a (?:? ?b))`                          | `(+ 1 2)`                         | `(1 2)`           |
| 52  | `'[(?:? ?x)]`                               | `[]`                              | `(nil)`           |
| 53  | `'[(?:? ?x)]`                               | `[1]`                             | `(1)`             |
| 54  | `'(+ (?:* ?x))`                             | `(+)`                             | `([])`            |
| 55  | `'(+ (?:* ?x))`                             | `(+ 1)`                           | `([1])`           |
| 56  | `'(+ (?:* ?x))`                             | `(+ 1 2 3)`                       | `([1 2 3])`       |
| 57  | `'(+ (?:+ ?x))`                             | `(+ 1)`                           | `([1])`           |
| 58  | `'(+ (?:+ ?x))`                             | `(+ 1 2 3)`                       | `([1 2 3])`       |
| 59  | `'(+ (?:+ ?x))`                             | `(+)`                             | `nil`             |
| 60  | `'(+ (?:n 2 ?x))`                           | `(+ 1 2)`                         | `([1 2])`         |
| 61  | `'(+ (?:n 2 ?x))`                           | `(+ 1 2 3)`                       | `nil`             |
| 62  | `'(+ (?:n [2 4] ?x))`                       | `(+ 1 2)`                         | `([1 2])`         |
| 63  | `'(+ (?:n [2 4] ?x))`                       | `(+ 1 2 3)`                       | `([1 2 3])`       |
| 64  | `'(+ (?:n [2 4] ?x))`                       | `(+ 1 2 3 4)`                     | `([1 2 3 4])`     |
| 65  | `'(+ (?:n [2 4] ?x))`                       | `(+ 1)`                           | `nil`             |
| 66  | `'(:a (?:chain ?x inc) :b ?x)`              | `(:a 1 :b 1)`                     | `(1)`             |
| 67  | `'(:a (?:as x [?a ?b]) :c ?x)`              | `(:a [1 2] :c [1 2])`             | `([1 2] 1 2)`     |
| 68  | `'(:a (?:as* x [?a ?b]) :c ?x)`             | `(:a [1 2] :c [1 2])`             | `([1 2])`         |
| 69  | `'(:a (?:as x ?v) :c ?x)`                   | `(:a 1 :c 1)`                     | `(1)`             |
| 70  | `'(:a (?:as* x ?v) :c ?x)`                  | `(:a 1 :c [1])`                   | `([1])`           |
| 71  | `'(?:or ?a ?b)`                             | `1`                               | `(1)`             |
| 72  | `'(?:or ?a ?b)`                             | `2`                               | `(2)`             |
| 73  | `'(?:and ?a ?b)`                            | `1`                               | `nil`             |
| 74  | `'(?:and ?a ?b)`                            | `(list 1 2)`                      | `(1 2)`           |
| 75  | `'(:a (?:not 1) ?x)`                        | `(:a 2 2)`                        | `(2)`             |
| 76  | `'(:a (?:not 1) ?x)`                        | `(:a 1 2)`                        | `nil`             |
| 77  | `'(:a (?:if number? ?x ?y) :b ?x)`          | `(:a 1 :b 1)`                     | `(1 nil)`         |
| 78  | `'(:a (?:if number? ?x ?y) :b ?y)`          | `(:a :x :b :x)`                   | `(nil :x)`        |
| 79  | `'(:a (?:when number? ?x ?y) :b ?y)`        | `(:a 1 2 :b 2)`                   | `(1 2)`           |
| 80  | `'(:a (?:when number? ?x ?y) :b ?y)`        | `(:a :x 2 :b 2)`                  | `nil`             |
| 81  | `'(?:letrec [A [?x ?y]] (:a $A :b ?z))`     | `(:a [1 2] :b 3)`                 | `(1 2 3)`         |
| 82  | `'(?:letrec [A [?x ?y]] (:a $A :b ?x))`     | `(:a [1 2] :b 1)`                 | `(1 2)`           |
| 83  | `'(?:letrec [A [?x ?y]] (:a $A :b ?y))`     | `(:a [1 2] :b 2)`                 | `(1 2)`           |
| 84  | `'(:a (?:fresh [x] [?x ?x]) ?x)`            | `(:a [1 1] 2)`                    | `(2)`             |
| 85  | `'(:a (?:fresh [x] [?x ?x]) ?x)`            | `(:a [1 2] 2)`                    | `nil`             |
| 86  | `'(?:re-matches #"(\d+)-(\d+)" [?_ ?a ?b])` | `"123-456"`                       | `("123" "456")`   |
| 87  | `'(?:re-seq #"(\d+)" [[?_ ?x] [?_ ?y]])`    | `"123 456"`                       | `("123" "456")`   |
| 88  | `'(:a (?:set ?x ?y) :b ?x)`                 | `(:a #{1 2} :b 1)`                | `(1 2)`           |
| 89  | `'(:a #{1 2})`                              | `(:a #{1 2})`                     | `()`              |
| 90  | `'(:a #{1 2})`                              | `(:a #{1 2 3})`                   | `()`              |
| 91  | `'(:a #{1 ?x} :b #{?x})`                    | `(:a #{1 2} :b #{2})`             | `(2)`             |
| 92  | `'(:a (?:map :x ?x :y ?y) :b ?x)`           | `(:a {:x 1 :y 2} :b 1)`           | `(1 2)`           |
| 93  | `'(:a (?:closed {:x 1 :y 2}))`              | `(:a {:x 1 :y 2})`                | `()`              |
| 94  | `'(:a (?:closed {:x 1 :y 2}))`              | `(:a {:x 1 :y 2 :z 3})`           | `nil`             |
| 95  | `'(:a (?:map :x 1 :y ?y) :b ?y)`            | `(:a {:x 1 :y {:z 1}} :b {:z 1})` | `({:z 1})`        |
| 96  | `'(?:*map ?k ?v)`                           | `{:a 1 :b 2}`                     | `([:a :b] [1 2])` |
| 97  | `'(?:nth 0 ?x)`                             | `(1 2 3)`                         | `(1)`             |
| 98  | `'(?:nth 1 ?x)`                             | `(1 2 3)`                         | `(2)`             |
| 99  | `'(?:nth ?i 3)`                             | `(1 2 3)`                         | `(2)`             |
| 100 | `'(?:nth ?i (?:as x [?_ 2]))`               | `([:a 1] [:b 2])`                 | `(1 [:b 2])`      |






## Rule-Based Transformation (R3)

Pattern's R3 system allows defining rewrite rules using the `rule` macro.

```clojure
(rule '(+ ?a ?b) (sub (* ?a ?b)))
```

### Combinators

R3 provides combinators for building complex rule sets:

* `rule-list`: Tries each rule in order.

* `rule-list!`: Like `rule-list`, but throws an exception if no rule matches.

* `in-order`: Runs rules in sequence, applying each successful rule's result to the next rule.

* `guard`:  Applies a rule only if a predicate is true.

* `n-times`: Applies a rule a specific number of times.

* `descend`:  Descends into sub-expressions.

* `descend-all`:  Descends into all elements of a sequence.

* `in`: Descends with an environment, discarding the resulting environment.

* `directed`:  Descends only into marked sub-expressions (e.g., `?->x`).

* `on-mutual`:  Applies different rules based on expression types.

* `on-subexpressions`: Applies a rule to all sub-expressions.

* `iterated`: Applies a rule repeatedly until no further changes are made.

* `simplifier`: Applies a rule repeatedly depth-first until no further changes.

* `prewalk-simplifier`: Applies a rule repeatedly, then prewalk descends until no further changes.

### Post-Processing

Post-processors can modify the result of a rule:

* `merge-metadata`: Merges metadata from the original value to the new value.

* `raw`: Disables default post-processing.

* `mark-success`:  Records successful rule applications in the environment.


## Substitution

* `sub`:  Perform static macro expansion of substitution patterns.

* `subm`: Perform substitution and attach metadata. `subm+` is used for generated expressions.

* `rmeta`: Accesses the metadata of the original matched expression.


## Nanopass Framework

The nanopass framework provides tools for defining language dialects and transformations between them.

* `def-dialect`: Defines a language dialect.

* `def-derived`: Creates a new dialect based on an existing one.

* `=>`, `==>`, `===>`:  Specify dialect pairs for transformations.

* `from-dialect`, `to-dialect`, `dialects`:  Wrap rules to specify dialects.

* `defpass`:  Defines a nanopass transformation.

* `let-rulefn`: Defines mutually recursive rules within a pass.

* `descend-into`:  Creates a rule-list for descending into valid expressions in a dialect.



This README provides a brief overview of the Pattern library. For more detailed information and examples, refer to the docstrings and tests within the source code.
