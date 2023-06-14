# Pattern

Pattern lets you transform data structures in amazing ways.

The focus is on simplicity and expressivity.
It works on immutable persistent data, greatly simplifying development and debugging of transformations.

``` clojure
pangloss/pattern {:git/url "https://github.com/pangloss/pattern"
                  :sha "<use the current commit hash>"}
```

## Video

[See my Nov 2022 talk for London Clojurians](https://www.youtube.com/watch?v=1V0VNBgWokA)

## How can this be used?

Here are a few examples of how it's been used already:

* Create simple and clear macros
* Create an infix math macro in about 30 LOC
* Define the simplification rules of a computer algebra system (see a very similar engine in use in SICMUtils)
* Create a Python to Clojure source-to-source converter in under 400 LOC
* Compile Scheme to X86 assembly in about 1500 LOC

The primary tools in Pattern are the rule and rule combinator.
To understand how to use those, it's important to first introduce matcher patterns and substitution.

## How does it work?

Pattern is an collection of tools for pattern matching and substitution.
Those tools can be extended and combined in flexible ways.

The match pattern looks similar to the data structure it's matching on.
That enables a very intuitive understanding of how the pattern will apply to the data being matched.

A transformation is a match pattern with a substitution pattern.
Combined, that is called a rule.

The substitution pattern uses exactly the same syntax as the match pattern.
Substitution supports all of core functionality of the matcher.
That makes it much simpler to understand the behavior of a rule.

In the spirit of Clojure, pattern maintains a high degree of simplicity in the interface.

## Pattern Matching

``` clojure
(require '[pattern :refer [compile-pattern]])
```

The core of Pattern is the pattern matcher, which can be used to match any kind of Clojure data structure.
To use the pattern matcher, call `(compile-pattern my-pattern)`. 
That returns a function that you can call with the data you want to extract matches from. 
The return value is a map from match names to matching data.

Here is a simple example that matches the first and last elements of a vector if the central elements are `1 2 3`.

``` clojure
(def m (compile-pattern '[?before 1 2 3 ?after])

(m [0 1 2 3 4]) ; => {:before 0 :after 4}
```

Even a simple pattern encodes sophisticated matching logic.
For instance you could replicate the above matcher with this code. 
As you can see, it's more complex, less clear in intention, and easier to make a mistake:

``` clojure
(def m #(when (vector? %)
          (if (and (= 5 (count %))
                (= [1 2 3] (subvec % 1 4)))
            {:before (first %)
             :after (last %)})))

(m [0 1 2 3 4]) ; => {:before 0 :after 4}
```

The advantages of these pattern matchers become even more apparent as the complexity of pattern increases.

### Unification Within a Pattern

If multiple matchers in a pattern have the same name, the values they match must unify.

Unification increases the sophistication of patterns that can be defined.

``` clojure
(def m (compile-pattern '[?fn-name (fn ?fn-name [??args] ??body)]))

(m ['abc '(fn abc [x] x)]) ; => {:fn-name 'abc ...}
(m ['xyz '(fn abc [x] x)]) ; => nil
```

Unification works across different matcher types.
The pattern `[?list [??list 3]]`, could match `[[1 2] [1 2 3]]` or `[[:x] [:x 3]]`, etc. 


### Pattern Matchers Available

Above I showed 2 matchers: `match-list` and `match-element` matching against a fixed-length vector. 
Much more flexibility is available.

The pattern could be changed to `[??before 1 2 3 ??after]`, for instance.
Now it would match a vector of any length as long as it contains the sequence `1 2 3`.

``` clojure
(def m* (compile-pattern '[??before 1 2 3 ??after]))

(m* [1 2 3])       ; => {:before [] :after []}
(m* [0 1 2 3 4 5]) ; => {:before [0] :after [4 5]}
```

Patterns also do not need to be flat.
For instance, I can match against Clojure S-Expressions. 
Here I'll introduce a three more matcher types:

``` clojure
(def let-bindings (compile-pattern '(let [(?:* (? binding* symbol?) ?_)] ??_)))

(let-bindings '(let [datum (first data)
                     c (count datum)]
                 ...))
;; => {:binding* [datum c]}
```

`?_` and `??_` are special cases of unnamed matchers.
These matchers do not unify with each other, and the value matched by them is not returned in the match results.
They are useful for ignoring parts of the input data that are not relevant to what you are trying to do.
Anywhere you can provide a matcher name, using `_` as the name has the same behavior.

The `?:*` matcher is `match-many`.
It matches a repeated subsequence within the sequence it is placed in.
In this case, that allows it to handle the characteristic flattened Clojure binding pattern.

The `(? ...)` matcher is the full form of `match-element` that we saw earlier. 
In this case, it is equivalent to `?binding*`, except that here I gave it a predicate function.
The matcher will only succeed if the predicate returns a truthy value when called with the matched value.

That means the following does not match:

``` clojure
(let-bindings '(let [42 (first data)
                     c (count datum)]
                 ...))
;; => nil
```

There are a lot more matchers and the list is gradually expanding with ever more weird and wonderful behaviors.

Each matcher in the list has a matcher implementation function with detailed documentation in the pattern.matchers namespace.

(better docs coming eventually!)

| Matcher         | Implementation     | Notes                                                                    |
|-----------------|--------------------|--------------------------------------------------------------------------|
| `?`             | match-element      | Match a single element                                                   |
| `??`            | match-segment      | Match 0 or more elements                                                 |
| `??!`           |                    | Same as `??`, but greedy                                                 |
| `?:map`         | match-map          | Match a map with specific keys                                           |
| `?:*map`        | match-*map         | Match each key-value pair in a map                                       |
| `?:+map`        | match-+map         | Like `?:*map`, but require at least one match                            |
| `?:as`          | match-as           | Capture an entire sub pattern if the contained pattern matches           |
| `?:?`           | match-optional     | Match 0 or 1 instance                                                    |
| `?:1`           | match-one          | Match exactly 1 instance                                                 |
| `?:*`           | match-many         | Match any number of instances                                            |
| `?:+`           | match-at-least-one | Match at least one instance                                              |
| `?:chain`       | match-chain        | Alternate between patterns and functions on the matched data             |
| `??:chain`      |                    | Same as `?:chain` but capture sequence data                              |
| `\|`            | match-or           | Match alternative patterns on the same data                              |
| `&`             | match-and          | Match all patterns on the same data                                      |
| `?:=`           | match-literal      | Match a literal value (needed if the form looks like a matcher pattern)  |
| `?:not`         | match-not          | Match only if the contained pattern does not                             |
| `?:when`        | match-when         | If the predicate, match the pattern                                      |
| `?:if`          | match-if           | If the predicate, match the then pattern, otherwise the else pattern     |
| `?:letrec`      | match-letrec       | Create named subpatterns that can be used later                          |
| `$`             | match-ref          | Use a named subpattern defined in `?:letrec`                             |
| `?:fresh`       | match-fresh        | Match a new copy of the given name                                       |
| `?:all-fresh`   | match-all-fresh    | Don't unify with captures outside the block                              |
| `?:restartable` | match-restartable  | If the pattern doesn't match, raise a condition that can provide a value |
| `?:re-matches`  | match-regex        | Match with a regex, binding captures                                     |
| `?:re-seq`      | match-regex        | Multiple matches with a regex, binding captures                          |
| `?:filter`      | match-filter       | Match only the items in the list where the predicate returns true        |
| `??:filter`     |                    | Inline sequence version of ?:filter                                      |
| `?:remove`      |                    | Match only the items in the list where the predicate returns false       |
| `??:remove`     |                    | Inline sequence version of ?:remove                                      |
    
      
#### A little about regex matchers


The `?:re-matches` pattern takes a second form which is a pattern that matches the structure
returned by `clojure.core/re-matches`:
``` clojure
(let [matcher (pattern/compile-pattern
                '(?:re-matches #"(\d+) (.+)" ?re-matches))]
  (matcher "123 [a b c]"))
``` 

That returned structure can itself be matched:
``` clojure
(let [matcher (pattern/compile-pattern
                '(?:re-matches #"(\d+) (.+)"
                   [?full_match ?group1 ?group2]))]
  (matcher "123 [a b c]"))
``` 

There is no way that I know of to discover group names, so here `foo` will not
be included in the bound names matched by the compiled pattern.
Here, `?foo` will bind to 999 just fine, because the named group in the regex
is not exposed outside of the regex itself.
``` clojure
(let [matcher (pattern/compile-pattern
                '[(?:re-matches #"(?<foo>\d+) (.+)"
                    [?full_match ?group1 ?group2])
                  ?foo])]
  (matcher ["123 [a b c]" "999"]))
``` 

Within the pattern, I can specify the name with ?foo, though. If I do then
the two instances must unify. This now fails to match:
``` clojure
(let [matcher (pattern/compile-pattern
                '[(?:re-matches #"(?<foo>\d+) (.+)"
                    [?full_match ?foo ?group2])
                  ?foo])]
  (matcher ["123 [a b c]" "999"]))
``` 

Named matches can still be useful in the regex and they together with all
features are perfectly acceptable to use.  Here the number at the beginning
and the end of the string must match for the regex to match.
``` clojure
(let [matcher (pattern/compile-pattern
                '(?:re-matches #"(?<foo>\d+) (.+) \k<foo>"
                   [?full_match ?group2 ?group1]))]
  (matcher "123 [a b c] 123"))
``` 

The captured data may have further matchers applied to it. Here I use the
?:chain matcher to parse the second group with read-string, then match within
the parsed form.
``` clojure
(let [matcher (pattern/compile-pattern
                '(?:re-matches #"(?<foo>\d+) (.+) \k<foo>"
                   [?full_match
                    ?group2
                    (?:chain ?group1 read-string [?x ?y ?z])]))]
  (matcher "123 [a b c] 123"))
```

### Adding new matchers

The ?:chain rule can often be used to create a custom matcher.
This is the implementation of the ?:map one, simplified to replace `sub` for
`quo`. `quo` is only needed internally within pattern to allow the system to
bootstrap itself.

This matcher starts with an unnamed matcher that ensures the matched datum is either a map or nil: `(? _ ~(some-fn nil? map?))`
Then if that matches, calls `seq` on that datum, turning the map into a list of `[key value]` pairs.
The result may match either `nil` if the map is empty, or each key value pair must match the given `k` and `v` pattern forms, which are spliced into the matcher here: `(| nil ((?:* [~k ~v])))`.

The generated matcher is then compiled with `compile-pattern*`, passing along the compilation environment.

Finally, new matchers must be registered with their name and optional aliases.

``` clojure
(defn match-*map
  "Create a ?:*map matcher than can match a key/value pair multiple times."
  [[_ k v] comp-env]
  (compile-pattern*
    (sub (?:chain
           (? _ ~(some-fn nil? map?))
           seq
           (| nil ((?:* [~k ~v])))))
    comp-env))

(register-matcher '?:*map #'match-*map {:aliases ['?:map*]})
```


## Substitution

The core substitution function is `sub`. 
It is actually a macro that expands to be equivalent to just writing the substitution pattern as a literal value.

``` clojure
(let [x 2
      y '[a b c]]
  (sub (* (+ ??y) ?x)))
;; => (* (+ a b c) 2)
```

Macroexpanded, you can see that the substitution overhead is effectively zero:

``` clojure
(let [x 2
      y '[a b c]] 
  (list '* (list* '+ y) x))
```

You may notice that instead of passing in a map of values to `sub`, it effectively looks in the current evaluation context for replacement values.
This tends to be very convenient. 
In practice, 99% of the time I use this method.

For that last 1%, though, a more traditional data-driven substitution method is required.
For that, we can use `substitute`, which interprets and executes the pattern at runtime:

``` clojure
(substitute 
  '(* (+ ??y) ?x)
  {'x 2 'y '[a b c]})
;; => (* (+ a b c) 2)
```

## Rules

Rules are pattern matchers tied to function bodies.
The captured data from the matcher becomes the function arguments.

Most frequently the function body is modifying data and thu `sub` macro is the perfect tool, but any value can be returned by a matching rule.


``` clojure
(rule mult-id
  '(* 1 ?x)
  x)
  
(rule strength-reduce
  '(* 2 ?x)
  (sub (+ ?x ?x)))
```

Rules are implemented in terms of standard matchers, so any of the above matchers may be used.

A rule or rule combinator can be called like a function.

``` clojure
(def my-rule (rule '(* 2 ?x) (sub (+ ?x ?x))))

(my-rule '(* 2 5)) # => (+ 5 5)
```

## Rule Combinators

Rule combinators allow multiple rules to be used together. 
Rule combinators can themselves be combined.
A rule combinator is itself just a rule. Rules and rule combinators are interchangeable.

The following combinators are documented for now in the pattern.r3.combinators namespace:

| Rule combinator | Note |
| --- | --- |
| rule-list | Search the rules from top to bottom. Stop after successfully matching. |
| in-order | Search the rules from top to bottom. Continue with the result of each matching rule. |
| on-subexpressions | Try the given rule on every element in the datastructure in post-walk order |
| iterated | Keep applying the rule until a fixed point is reached |
| simplifier | Like on-subexpressions which iterates at every level |
| directed | Guide the traversal either using the pattern or from within the rule body |


## Compilation Dialects and Tools

...

## Acknowledgements

Pattern is based upon the core ideas described in the excellent book [Software Design for Flexibilty](https://mitpress.mit.edu/books/software-design-flexibility) by Chris Hanson and Gerald Jay Sussman.

The compilation tools aspect is heavily inspired by the [Nanopass Framework](https://nanopass.org/) which introduces the idea of dialects and was the inspiration for some of the more powerful rule combinators that this library introduces.

## License

Copyright © 2022 Darrick Wiebe

_Distributed under the Eclipse Public License version 1.0._
