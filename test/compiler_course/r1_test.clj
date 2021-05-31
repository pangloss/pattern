(ns compiler-course.r1-test
  (:require [compiler-course.r1-allocator :as a]
            [compiler-course.r1 :refer :all]
            [compiler-course.dialects :as d]
            [clojure.test :refer [deftest testing is]]))

;; TODO: make some real tests; port the test cases from the course notes.

(comment

  (meta (:validate d/Shrunk))

  ((:validate d/Shrunk)
   (->shrink
    '(+ (- y) 1)))

  ((:validate d/Simplified)
   (->simple
    '(let ([x 1])
       (let ([y 2])
         (if (if (< x y)
               (eq? (- x) (+ x (+ y 0)))
               (eq? x 2))
           (+ y 2)
           (+ y 10))))))

  ((:validate d/Explicit)
   '(program
     [x.1 y.2 tmp-.3 tmp+.4 tmp+.5]
     {then.8
      (block
       then.8
       [tmp-.3 tmp+.4 tmp+.5]
       (assign tmp-.3 (- x.1))
       (assign tmp+.4 (+ y.2 0))
       (assign tmp+.5 (+ x.1 tmp+.4))
       (if (eq? tmp-.3 tmp+.5) (goto then.6) (goto else.7))),
      else.9 (block else.9 [] (if (eq? x.1 2) (goto then.6) (goto else.7))),
      then.6 (block then.6 [] (return (+ y.2 2))),
      else.7 (block else.7 [] (return (+ y.2 10))),
      start
      (block
       start
       [x.1 y.2 tmp-.3 tmp+.4 tmp+.5]
       (assign x.1 1)
       (assign y.2 2)
       (if (< x.1 y.2) (goto then.8) (goto else.9)))}))
   



  (let [x
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
                                             (if
                                                 ;; This deepest if statement is one of 2 that would get double-finalized
                                                 (if (eq? a y)
                                                   (not (eq? (- a) (+ (- a) (+ y 0))))
                                                   (not (eq? a 2)))
                                               (+ (+ 1 (+ a (+ b (+ c (+ d ( + e (+ f (+ g (+ y 2)))))))))
                                                  (+ 1 (+ a' (+ b' (+ c' (+ d' ( + e' (+ f' (+ y' 2)))))))))
                                               (+ y 10))))))))))))))))))))]
    [;;(explicate-control (remove-complex-opera* (shrink (uniqify x))))
     ((:validate d/Explicit)
      (->flatten x))])


  (->patch '(if a (if c 4 5) (if b 2 3)))

  (->jump '(if a (if c 4 5) (if b 2 3)))

  (->compile '(if a (if c 4 5) (if b 2 3)))

  ;;
  (let [a '(let ([x 1]) (if (eq? 1 x) 42 0))
        r '(if (eq? 1 (read)) 42 0)]
    [(->compile a)
     (->compile r)])


  (->compile
   '(if false 1 2))

  (->flatten
   '(if (if (if (eq? a a)
              (> a b)
              (> x y))
          true
          (eq? c 2))
      (+ d 2)
      (+ e 10)))

  (do (reset! niceid 0)
      [(a/allocate-registers
        (select-instructions
         (explicate-control
          (remove-complex-opera*
           (shrink
            '(if (if (if (let ([z (> (+ 1 (- 1)) (+ 2 (- 2)))]) z)
                       (< x y)
                       (> x y))
                   (eq? (- x) (+ x (+ y 0)))
                   (eq? x 2))
               (+ y 2)
               (+ y 10)))))))
       (reset! niceid 0)
       (a/liveness
        (select-instructions
         (explicate-control
          (remove-complex-opera*
           (shrink
            '(let ([x 1])
               (let ([y 2])
                 (if (if (if (> x y)
                           (< x y)
                           (> x y))
                       (eq? (- x) (+ x (+ y 0)))
                       (eq? x 2))
                   (+ y 2)
                   (+ y 10)))))))))])

  ()
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
               (+ y 10))))))))))


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


  (select-instructions
   (explicate-control
    (remove-complex-opera*
     (shrink
      '(not (< a b))))))

  (select-instructions
   (explicate-control
    (remove-complex-opera*
     (shrink
      '(if a
         1 2)))))

  (select-instructions
   (explicate-control
    (remove-complex-opera*
     (shrink
      '(if (if (if (not (not false))
                 (< x y)
                 (> x y))
             (eq? (- x) (+ x (+ y 0)))
             (eq? x 2))
         (+ y 2)
         (+ y 10)))))

   ,)

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
