(ns compiler-course.r1-test
  (:require [compiler-course.r1-allocator :as a]
            [compiler-course.r1 :refer :all]
            [matches :refer [valid? validate ok?]]
            [compiler-course.dialects :as d]
            [clojure.test :refer [deftest testing is are]]))

(def passes
  (partition 2
             [#'identity #'d/R1
              #'uniqify #'d/R1
              #'shrink #'d/Shrunk
              #'remove-complex-opera* #'d/Simplified
              #'explicate-control #'d/Explicit
              #'select-instructions #'d/Selected
              #'allocate-registers #'d/Allocated
              #_#_
              #'remove-jumps #'d/NoJumps
              #_#_#_#_
              #'patch-instructions #'d/Patched
              #'save-registers #'d/Patched
              #_#_
              #'stringify #'d/Strings]))


(defn test-pipeline [form]
  (loop [form form [[pass dialect] & more] passes]
    (let [result (pass form)
          v (validate @dialect result)]
      (if (ok? v)
        (if more
          (recur result more)
          v)
        v))))

(defn test-pipeline! [form]
  (loop [form form [[pass dialect] & more] passes results []]
    (let [result (pass form)
          results (conj results result)
          v (validate @dialect result)]
      (if (ok? v)
        (if more
          (recur result more results)
          v)
        (conj results v)))))

(def iffy-program
  '(let ([x 1])
     (let ([y 2])
       (if (if (< x y)
             (eq? (- x) (+ x (+ y 0)))
             (eq? x 2))
         (+ y 2)
         (+ y 10)))))


(def iffier-program
  '(if (if (if (let ([z (> (+ 1 (- 1)) (+ 2 (- 2)))]) z)
             (< x y)
             (> x y))
         (eq? (- x) (+ x (+ y 0)))
         (eq? x 2))
     (+ y 2)
     (+ y 10)))


(deftest compile-iffy-programs
  (is (ok? (test-pipeline iffy-program)))
  (is (ok? (test-pipeline iffier-program))))

(def spilly-program
  '(let ([x 1])
     (let ([y 0])
       (let ([a 0])
         (let ([b 0])
           (let ([c 0])
             (let ([d 0])
               (let ([e 0])
                 (let ([f 0])
                   (let ([g 0])
                     (if (if (eq? x y)
                           (not (eq? (- x) (+ (- x) (+ y 0))))
                           (not (eq? x 2)))
                       (+ 1 (+ a (+ b (+ c (+ d ( + e (+ f (+ g (+ y 2)))))))))
                       (let ([x 1])
                         (let ([y' 1])
                           (let ([a' 1])
                             (let ([b' 1])
                               (let ([c' 1])
                                 (let ([d' 1])
                                   (let ([e' 1])
                                     (let ([f' 1])
                                       (if (if (eq? a y)
                                             (not (eq? (- a) (+ (- a) (+ y 0))))
                                             (not (eq? a 2)))
                                         (+ (+ 1 (+ a (+ b (+ c (+ d ( + e (+ f (+ g (+ y 2)))))))))
                                            (+ 1 (+ a' (+ b' (+ c' (+ d' ( + e' (+ f' (+ y' 2)))))))))
                                         (+ y 10)))))))))))))))))))))

(deftest compile-spilly-program
  (is (ok? (test-pipeline spilly-program))))


(deftest various-programs
  (are [p] (ok? (test-pipeline p))

    '(if a (if c 4 5) (if b 2 3))

    '(let ([x 1]) (if (eq? 1 x) 42 0))

    '(if (eq? 1 (read)) 42 0)

    '(if (if (if (eq? a a)
               (> a b)
               (> x y))
           true
           (eq? c 2))
       (+ d 2)
       (+ e 10))

    '(let ([x 1])
       (let ([y 2])
         (if (if (if (> x y)
                   (< x y)
                   (> x y))
               (eq? (- x) (+ x (+ y 0)))
               (eq? x 2))
           (+ y 2)
           (+ y 10))))

    '(if (if (if (not (not false))
               (< x y)
               (> x y))
           (eq? (- x) (+ x (+ y 0)))
           (eq? x 2))
       (+ y 2)
       (+ y 10))

    '(let ([a 1])
       (let ([b 2])
         (not (< a b))))

    '(if (if (< (- x) (+ x (+ y 2)))
           (eq? (- x) (+ x (+ y 0)))
           (eq? x 2))
       (+ y 2)
       (+ y 10))

    '(let ([a true])
       (if a 1 2))))


(comment
  (println
   (stringify
    (a/patch-instructions
     (a/allocate-registers
      (select-instructions
       (explicate-control
        (remove-complex-opera*
         (shrink
          (uniqify
           '(let ([x 1])
              (let ([y 2])
                (if (if (if (> x y)
                          (< x y)
                          (> x y))
                      (eq? (- x) (+ x (+ y 0)))
                      (eq? x 2))
                  (+ y 2)
                  (+ y 10)))))))))))))

  (comment
    (remove-complex-operations
     (shrink
      (uniqify
       '(program (let ([x 32]) (eq? (let ([x 10]) x) x))))))

    (explicate-pred (remove-complex-operations (shrink (uniqify '(program (<= (+ 1 2) 2))))))

    (remove-complex-operations
     '(program
       (if (eq? x 2)
         (+ y 2)
         (+ y 10))))

    (explicate-expressions
     (remove-complex-operations
      '(program (if (if (< (- x) (+ x (+ y 2)))
                      (eq? (- x) (+ x (+ y 0)))
                      (eq? x 2))
                  (+ y 2)
                  (+ y 10))))))


  (comment
    (remove-complex-operations '(program (let ([x (+ 2 (- 1))]) (+ x 2))))

    [(explicate-expressions)
     (remove-complex-operations
      '(program (let ([x (+ 2 (- 1))]) (+ x 2))))]

    (flatten
     '(program (let ([x (+ 2 (- 1))]) (+ x 2))))


    [(uniqify '(program (let ([x 32]) (+ (let ([x 10]) x) x))))]

    [(uniqify '(program (let ([x 32]) (+ 10 x))))]

    ,
    (flatten (uniqify '(program (let ([x 32]) (+ (let ([x 10]) x) x)))))
    (fu
     '(program
       (let ([x (+ (- (read)) 11)])
         (+ x 41))))

    (fu '(program (let ([a 42])
                    (let ([b a])
                      b))))

    (fu '(program (let ([a 42])
                    (let ([b a])
                      b))))

    (fu '(program (let ([x 32]) (+ 10 x))))

    (sfu '(program (let ([x 32]) (+ (let ([x (- 10)]) x) x))))

    (sfu
     '(program
       (let ([x (+ (- (read)) 11)])
         (+ x 41))))

    (sfu '(program (let ([a 42])
                     (let ([b a])
                       b))))

    [(fu '(program (let ([x 32]) (+ (- 10) x))))
     (sfu '(program (let ([x 32]) (+ (- 10) x))))]
    ,
    (asfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

    (asfu
     '(program
       (let ([x (+ (- (read)) 11)])
         (+ x 41))))

    (asfu '(program (let ([a 42])
                      (let ([b a])
                        b))))

    [(fu '(program (let ([x 32]) (+ (- 10) x))))
     (sfu '(program (let ([x 32]) (+ (- 10) x))))
     (asfu '(program (let ([x 32]) (+ (- 10) x))))]
    ,
    (pasfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

    (pasfu
     '(program
       (let ([x (+ (- (read)) 11)])
         (+ x 41))))

    (pasfu '(program (let ([a 42])
                       (let ([b a])
                         b))))

    [(fu '(program (let ([x 32]) (+ (- 10) x))))
     (sfu '(program (let ([x 32]) (+ (- 10) x))))
     (asfu '(program (let ([x 32]) (+ (- 10) x))))
     (pasfu '(program (let ([x 32]) (+ (- 10) x))))]
    ,
    (spasfu '(program (let ([x 32]) (+ (let ([x 10]) x) x))))

    (spasfu
     '(program
       (let ([x (+ (- (read)) 11)])
         (+ x 41))))

    (spasfu '(program (let ([a 42])
                        (let ([b a])
                          b))))

    [(fu '(program (let ([x 32]) (+ (- 10) x))))
     (sfu '(program (let ([x 32]) (+ (- 10) x))))
     (asfu '(program (let ([x 32]) (+ (- 10) x))))
     (pasfu '(program (let ([x 32]) (+ (- 10) x))))
     (spasfu '(program (let ([x 32]) (+ (- 10) x))))]
    ,)
  (comment

    (pasfu '(program
             (let ([v 1])
               (let ([w 42])
                 (let ([x (+ v 7)])
                   (let ([y x])
                     (let ([z (+ x w)])
                       (+ z (- y)))))))))

    (pasfu '(program
             (let ([x1 (read)])
               (let ([x2 (read)])
                 (+ (+ x1 x2)
                    42)))))


    (println
     (r1/stringify
      (allocate-registers
       '(program (...)
                 (movq (int 1) (v v))
                 (movq (int 42) (v w))
                 (movq (v v) (v x))
                 (addq (int 7) (v x))
                 (movq (v x) (v y))
                 (movq (v x) (v z))
                 (addq (v w) (v z))
                 (movq (v y) (v t))
                 (negq (v t))
                 (movq (v z) (reg rax))
                 (addq (v t) (reg rax))
                 (movq (int 1) (v c))
                 (addq (v c) (v c))
                 (jmp conclusion)))))

    (def ex
      ;; why can't I just directly def ex????
      (let [ex
            (liveness
             '(program (...)
                       (movq (int 1) (v v))
                       (movq (int 42) (v w))
                       (movq (v v) (v x))
                       (addq (int 7) (v x))
                       (movq (v x) (v y))
                       (movq (v x) (v z))
                       (addq (v w) (v z))
                       (movq (v y) (v t))
                       (negq (v t))
                       (movq (v z) (reg rax))
                       (addq (v t) (reg rax))
                       (movq (int 1) (v c))
                       (addq (v c) (v c))
                       (jmp conclusion)))]
        ex))

    ex

    (let [g (to-graph ex)
          g (allocate-registers* g)]
      (->> (f/all-vertices g)
           (sort-by order)
           (map (juxt identity saturation movedness (comp get-location color)))))

    (liveness
     '(program
       (x.1 x.2 tmp+.3)
       (movq (int 32) (v x.1))
       (movq (int 10) (v x.2))
       (movq (v x.2) (v tmp+.3))
       (addq (v x.1) (v tmp+.3))
       (movq (v tmp+.3) (reg rax))
       (retq)))

    ,))
