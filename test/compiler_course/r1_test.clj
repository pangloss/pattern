(ns compiler-course.r1-test)

;; TODO: make some real tests; port the test cases from the course notes.
(comment
  (select-instructions
   (explicate-control
    (remove-complex-opera*
     '(if (if (< x y)
            (eq? (- x) (+ x (+ y 0)))
            (eq? x 2))
        (+ y 2)
        (+ y 10)))))

  (select-instructions
   (explicate-control
    (remove-complex-opera*
     '(if (if false
            (eq? (- x) (+ x (+ y 0)))
            (eq? x 2))
        (+ y 2)
        (+ y 10)))))


  (select-instructions
   (explicate-control
    (remove-complex-opera*
     '(if false 1 2))))

  (explicate-control
   (remove-complex-opera*
    (shrink
     '(if (if (if (eq? a a)
                (> a b)
                (> x y))
            true
            (eq? c 2))
        (+ d 2)
        (+ e 10)))))

  (do (reset! niceid 0)
      [(select-instructions
        (explicate-control
          (remove-complex-opera*
           (shrink
            '(if (if (if (let ([z (> (+ 1 (- 1)) (+ 2 (- 2)))]) z)
                       (< x y)
                       (> x y))
                   (eq? (- x) (+ x (+ y 0)))
                   (eq? x 2))
               (+ y 2)
               (+ y 10))))))
       (reset! niceid 0)
       (select-instructions
        (explicate-control
         (remove-complex-opera*
          (shrink
           '(if (if (if (> x y)
                      (< x y)
                      (> x y))
                  (eq? (- x) (+ x (+ y 0)))
                  (eq? x 2))
              (+ y 2)
              (+ y 10))))))])

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
         (+ y 10))))))

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

  ,)
