# Pattern

Pattern matching system

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
