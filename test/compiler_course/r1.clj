(ns compiler-course.r1
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  caller-saved-registers callee-saved-registers
                                                  var-locations with-allocated-registers]]
            [compiler-course.dialects :refer [r1-keyword?]]
            [pattern.nanopass.dialect :refer [all-dialects =>:to show-parse]]
            [pattern :refer [descend in gennice niceid directed on-subexpressions rule rule-list rule-list!
                             descend-all sub success subm rule-simplifier matcher
                             => dialects validate ok ok?]]
            [pattern.types :refer [child-rules]]
            [clojure.string :as str]
            [compiler-course.pass01-uniqify :refer [uniqify]]
            [compiler-course.pass02-shrink :refer [shrink]]
            [compiler-course.pass03-expose-functions :refer [expose-functions]]
            [compiler-course.pass04-limit-functions :refer [limit-functions]]
            [compiler-course.pass05-convert-closures :refer [convert-closures]]
            [compiler-course.pass06-add-types :refer [add-types]]
            [compiler-course.pass07-expose-allocation :refer [expose-allocation]]
            [compiler-course.pass08-remove-complex-opera :refer [remove-complex-opera*]]
            [compiler-course.pass09-explicate-control :refer [explicit-control-flow]]
            [compiler-course.pass10-uncover-locals :refer [uncover-locals]]
            [compiler-course.pass11-select-instructions :refer [select-instructions]]
            [compiler-course.pass12-allocate-registers :refer [allocate-registers]]
            [compiler-course.pass13-remove-unallocated :refer [remove-unallocated]]
            [compiler-course.pass14-remove-jumps :refer [remove-jumps]]
            [compiler-course.pass15-patch-instructions :refer [patch-instructions]]
            [compiler-course.pass16-save-registers :refer [save-registers]]
            [compiler-course.pass17-stringify :refer [stringify]]))


(def passes
  [#'uniqify
   #'shrink
   #'expose-functions
   #'limit-functions
   #'convert-closures
   #'add-types
   #'expose-allocation
   #'remove-complex-opera*
   #'explicit-control-flow
   #'uncover-locals
   #'select-instructions
   #'allocate-registers
   #'remove-unallocated
   #'remove-jumps
   #'patch-instructions
   #'save-registers])

(defn valid-asm? [p]
  (when (sequential? p)
    (every? #(and (sequential? %)
                  (every? string? %))
            p)))

;; TODO: adopt this or something similar into nanopass.
(defn tester [start-dialect passes finalize valid-output?]
  (fn [form]
    (loop [form form [pass & more] (cons identity passes) results []]
      (let [dialect (if (= identity pass)
                      start-dialect
                      (or (=>:to (meta pass) nil)
                          (=>:to (meta @pass) nil)))
            dialect (if (symbol? dialect)
                      (@all-dialects dialect)
                      dialect)
            result (try (pass form)
                        (catch Exception e {:error e}))
            results (conj results [pass (:name dialect) result])
            v (when dialect
                (when-not (:error result) (validate dialect result)))]
        (if (or (and (ok? v)) (not dialect))
          (if more
            (recur result more results)
            (let [s (finalize result)]
              (if (valid-output? s)
                v
                s)))
          (vec (reverse (conj results v))))))))

(def test-pipeline (tester 'R1 passes stringify valid-asm?))

(defn ->pass
  ([pass]
   (let [pass (if (int? pass) (nth passes pass) pass)]
     (with-meta
       (tester 'R1 (take-while #(and (not= pass %) (not= pass (deref %))) passes)
               pass
               (constantly false))
       {:pass pass})))
  ([pass form]
   (let [f (->pass pass)]
     [(meta f) (f form)])))



(comment
  (test-pipeline
   '
   [(define (add [x Integer] [y  Integer])  Integer (+ x y))
    (define (sub [x Integer] [y  Integer])  Integer (- x y))

    (+ (add 20 1)
       (let ([f (if (eq? (read) 0) add sub)])
         (f 20 1)))])

  (stringify
   (last
    (->pass 15 '[(define (abc [x Integer]) Integer
                   (abc 1))
                 (let ([a 1])
                   (+ ((lambda ([x Integer]) Integer (+ a x)) (abc 1))
                      99))])))

  (test-pipeline '[(define (abc [x Integer]) Integer
                     (abc 1))
                   (let ([a 1])
                     (+ ((lambda ([x Integer]) Integer (+ a x)) (abc 1))
                        99))]))
