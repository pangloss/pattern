(ns compiler-course.pass02-shrink
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  caller-saved-registers callee-saved-registers
                                                  var-locations with-allocated-registers]]
            [compiler-course.dialects :refer [r1-keyword?]]
            [matches.nanopass.dialect :refer [all-dialects =>:to show-parse]]
            [matches :refer [descend in gennice niceid directed on-subexpressions rule rule-list rule-list!
                             descend-all sub success subm rule-simplifier matcher
                             => dialects validate ok ok?]]
            [matches.types :refer [child-rules]]
            [clojure.string :as str]))


;; Shrink the number of instructions we need to support (by expanding to equivalent expressions)

(def immutable-expr?*
  "If the expression is immutable, the result will be unmodified.
   If the expression is mutable, the result will be modified."
  (on-subexpressions
   ;; NOTE: all expressions that either mutate or read mutable data must be captured here:
   ;; NOTE: this isn't perfect because it doesn't distinguish (future) quoted expressions, but that could be added.
   (rule-list (rule '(read) (success nil))
              (rule '(vector-ref ??_) (success nil))
              (rule '(vector-set! ??_) (success nil)))))

(defn immutable-expr? [exp]
  (= exp (immutable-expr?* exp)))

(def shrink
  (dialects
   (=> R1Fun Shrunk)
   (let [preserve-order (fn [n a b expr]
                          (let [t (gennice n)]
                            (sub (let ([?t ?a])
                                   ~(expr t)))))]
     (directed
      (rule-list
       (rule '(program ??->define))
       (rule '(define ?form ?type ?->e:body))
       (rule '(eq? ?->same ?->same)
             (if (immutable-expr? same)
               true
               (sub (eq? ?same ?same))))
       (rule '(- ?->e:a ?->e:b) (sub (+ ?a (- ?b))))
       (rule '(or ?->e:a ?->e:b) (sub (if ?a true ?b)))
       (rule '(and ?->e:a ?->e:b) (sub (if ?a (if ?b true false) false)))
       (rule '(if ?->e:exp ?->same ?->same)
             (if (and (immutable-expr? exp)
                      (immutable-expr? same))
               (success same)
               (sub (if ?exp ?same ?same))))
       ;; < is our canonical choice, so alter <= > >=
       (rule '(<= ?->e:a ?->e:b)
             (preserve-order 'le a b #(sub (not (< ?b ~%)))))
       (rule '(> ?->e:a ?->e:b)
             (preserve-order 'gt a b #(sub (< ?b ~%))))
       (rule '(>= ?->e:a ?->e:b)
             (sub (not (< ?a ?b))))
       (rule '((?:= let) ([?v ?->e]) ?->e:body))
       (rule '(if ?->e ?->e:then ?->e:else))
       (rule '(- ?->e))
       (rule '(+ ?->e0 ?->e1))
       (rule '(not ?->e))
       (rule '(?cmp ?->e0 ?->e1))
       (rule '(vector ??->e*))
       (rule '(vector-length ?->e))
       (rule '(vector-ref ?->e ?i))
       (rule '(vector-set! ?->e0 ?i ?->e1))
       (rule '(void))
       (rule '(read))
       (rule '((lambda ([?v* ?type*] ...) ?type ?->e) ??->arg*)
             (reduce (fn [e [v arg]]
                       (sub (let ([?v ?arg]) ?e)))
                     e (reverse (map vector v* arg*))))
       (rule '(lambda (??argdef*) ?type ?->e))
       (rule '(?->e:f ??->e:args)
             ;;(when-not (r1-keyword? f)
             ;; I don't try to handle if a fn shadows a built-in...
             (sub (call ?f ??args))))))))
