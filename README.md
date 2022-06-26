# Pattern

Pattern is an extensible pattern matching, substitution, and rules engine.

``` clojure
pangloss/pattern {:git/url "https://github.com/pangloss/pattern"
                  :sha "<use the current commit hash>"}
```

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

### Unification

If multiple matchers in a pattern have the same name, the values they match must unify.

Unification increases the sophistication of patterns that can be defined.

``` clojure
(def m (compile-pattern '[?fn-name (fn ?fn-name [??args] ??body)]))

(m ['abc '(fn abc [x] x)]) ; => {:fn-name 'abc ...}
(m ['xyz '(fn abc [x] x)]) ; => nil
```

Unification works across different matcher types.
The pattern `[?list [??list 3]`, could match `[[1 2] [1 2 3]]` or `[[:x] [:x 3]]`, etc. 


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
Here I'll introduce a two more matcher types:

``` clojure
(def let-bindings (compile-pattern '(let [(?:* (? binding* symbol?) ?_)] ??_)))

(let-bindings '(let [datum (first data)
                     c (count datum)]
                 ...))
;; => {:binding* [datum c]}
```

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

We also use `?_` and `??_` in the pattern. In both cases, the single _ name signals for the matcher to
discard the captured value.


Here is the full list of matchers available.

``` clojure
(register-matcher :value match-value)
(register-matcher :list #'match-list)
(register-matcher '?:= match-literal {:aliases ['?:literal]})
(register-matcher :compiled-matcher match-compiled)
(register-matcher :compiled*-matcher match-compiled*)
(register-matcher :plain-function #'match-plain-function)
(register-matcher '? #'match-element {:named? true})
(register-matcher '?? #'match-segment {:named? true})
(register-matcher '?:map match-map)
(register-matcher '?:+map #'match-+map)
(register-matcher '?:*map #'match-*map)
(register-matcher '?:as match-as {:named? true :restriction-position 3})
(register-matcher '?:? #'match-optional {:aliases ['?:optional]})
(register-matcher '?:1 #'match-one {:aliases ['?:one]})
(register-matcher '?:* #'match-many {:aliases ['?:many]})
(register-matcher '?:+ #'match-at-least-one {:aliases ['?:at-least-one]})
(register-matcher '?:chain match-chain {:aliases ['??:chain]})
(register-matcher '| #'match-or {:aliases ['?:or]})
(register-matcher '& match-and {:aliases ['?:and]})
(register-matcher '?:not match-not)
(register-matcher '?:if #'match-if)
(register-matcher '?:when #'match-when)
(register-matcher '?:letrec match-letrec)
(register-matcher '?:ref match-ref {:named? true})
(register-matcher '?:fresh #'match-fresh)
(register-matcher '?:all-fresh #'match-all-fresh)
(register-matcher '?:restartable match-restartable)
(register-matcher '?:re-matches #'match-regex)
(register-matcher '?:re-seq #'match-regex)

```

## Substitution

## Rules

## Rule Combinators

## Compilation Dialects and Tools


## Credits

and nanopass-style compilation

Pattern is based upon the core ideas described in the excellent book (Software Design for Flexibilty)[https://mitpress.mit.edu/books/software-design-flexibility] by Chris Hanson and Gerald Jay Sussman.

The compilation tools aspect is heavily inspired by the (Nanopass Framework)[https://nanopass.org/] which introduces the idea of dialects and was the inspiration for some of the more powerful rule combinators that this library introduces.

## Usage

Basic rule expression:

``` clojure
    (def simplify-zero (rule '(+ 0 ??n) (sub (+ ??n)))
    
    (simplify-zero '(+ 0 1 2 3)) ;; => (+ 1 2 3)
```

More examples coming soon...

## License

Copyright © 2021 Darrick Wiebe

TBD:
_Distributed under the Eclipse Public License version 1.0._
