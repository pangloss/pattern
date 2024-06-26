(ns compiler-course.r1-test
  (:require [compiler-course.r1-allocator :as a]
            [compiler-course.r1 :as r1 :refer :all]
            [compiler-course.dialects :refer [niceid]]
            [compiler-course.pass06-add-types :refer [add-types]]
            [compiler-course.pass07-expose-allocation :refer [expose-allocation]]
            [pattern :refer [valid? validate ok? sub subm]]
            [pattern.types :refer [ok]]
            [compiler-course.dialects :as d]
            [clojure.test :refer [deftest testing is are]]
            [clojure.walk :as walk]))

(def iffy-program
  '(let ([x 1])
     (let ([y 2])
       (if (if (< x y)
             (eq? (- x) (+ x (+ y 0)))
             (eq? x 2))
         (+ y 2)
         (+ y 10)))))

(def iffier-program
  '(let ([x 9])
     (let ([y 11])
       (if (if (if (let ([z (> (+ 1 (- 1)) (+ 2 (- 2)))]) z)
                 (< x y)
                 (> x y))
             (eq? (- x) (+ x (+ y 0)))
             (eq? x 2))
         (+ y 2)
         (+ y 10)))))

#_ ;; broken because of removal of scheme-style repeats.
(deftest compile-iffy-programs
  (is (= ok (test-pipeline iffy-program)))
  (is (= ok (test-pipeline iffier-program))))

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

#_ ;; broken because of removal of scheme-style repeats.
(deftest compile-spilly-program
  (is (= ok (test-pipeline spilly-program))))

(def veccy-program
  '(let ([t (vector 40 99 true (vector 2))])
     (if (vector-ref t 1)
       (+ (vector-ref t 0)
          (vector-ref (vector-ref t 3) 0))
       44)))

#_ ;; broken because of removal of scheme-style repeats.
(deftest test-vecs
  (is (= ok (test-pipeline veccy-program))))

(def fprogram
  '[(define (z [a Integer] [b Integer] [c Integer] [d Integer] [e Integer]
               [f Integer] [g Integer] [h Integer] [i Integer] [j Integer]) Integer
      (let ([j 1])
        (vector (z 1 2 3 4 5 6 7 0 0 0)
                (z a b c d e f g h i j)
                123)))
    (let ([j 1])
      (z j j j j j j j j j j))])

#_ ;; broken because of removal of scheme-style repeats.
(deftest test-f
  (is (= ok (test-pipeline fprogram))))

(def add-fun
  '[(define (add [x Integer] [y Integer]) Integer
      (+ x y))
    (add 40 2)])

#_ ;; broken because of removal of scheme-style repeats.
(deftest test-add-fun
  (is (= ok (test-pipeline add-fun))))

#_ ;; broken because of removal of scheme-style repeats.
(deftest various-programs
  (are [p] (= ok (test-pipeline p))

    '(let ([a true])
       (let ([b false])
         (let ([c true])
           (if a (if c 4 5) (if b 2 3)))))

    '(if (let ([x 1])
           (eq? 2 1))
       1 2)


    '(if (let ([x (void)])
           (eq? 2 1))
       1 2)


    '(let ([t (vector 40 true 2)])
       (if (vector-ref t 1)
         (+ (vector-ref t 0)
           (vector-ref t 2))
         44))

    '(let ([t (vector 40 true 2)])
       (vector-ref t 1))

    '(vector 40)

    '(if (eq? 1 (read)) 42 0)

    '(let ([a true])
       (let ([b false])
         (let ([c true])
           (let ([d true])
             (let ([e false])
               (let ([x true])
                 (let ([y true])
                   (if (if (if (eq? a a)
                             (> a b)
                             (> x y))
                         true
                         (eq? c 2))
                     (- d 2)
                     (+ e 10)))))))))

    '(let ([x 1111])
       (let ([y 2])
         (if (if (if (> x y)
                   (< x y)
                   (> x y))
               (eq? (- x) (+ x (+ y 0)))
               (eq? x 2))
           (+ y 2)
           (+ y 10))))

    '(let ([x 123])
       (let ([y 33])
         (if (if (if (not (not false))
                   (< x y)
                   (> x y))
               (eq? (- x) (+ x (+ y 0)))
               (eq? x 2))
           (+ y 2)
           (+ y 10))))

    '(let ([a 1])
       (let ([b 2])
         (not (< a b))))

    '(let ([x 123])
       (let ([y 33])
         (if (if (< (- x) (+ x (+ y 2)))
               (eq? (- x) (+ x (+ y 0)))
               (eq? x 2))
           (+ y 2)
           (+ y 10))))

    '(let ([a true]) (if a 1 2))

    '(let ([x (+ 2 (- 1))]) (+ x 2))

    '(let ([x (+ (- (read)) 11)])
       (+ x 41))

    '(let ([a 42]) (let ([b a]) b))

    '(let ([x 32]) (+ 10 x))

    '(let ([x 32]) (+ (- 10) x))

    '(let ([x 32]) (+ (let ([x 10]) x) x))

    '(let ([x 32]) (+ (let ([x (- 10)]) x) x))

    '(let ([v 1])
       (let ([w 42])
         (let ([x (+ v 7)])
           (let ([y x])
             (let ([z (+ x w)])
               (+ z (- y)))))))

    '(<= (+ 1 2) 2)

    '(let ([x1 (read)])
       (let ([x2 (read)])
         (+ (+ x1 x2)
           42)))))

(deftest splatter-vec
  (reset! niceid 0)
  (is (= '(+ 1
            (let ([entry.1 1])
              (let ([entry.2 2])
                (let ([__.4 (if (< (+ (global-value free_ptr) 24)
                                  (global-value fromspace_end))
                              (void) (collect 24))])
                  (let ([vector.3 (allocate 2 (Vector Integer Integer))])
                    (let ([__.5 (vector-set! vector.3 1 entry.2)])
                      (let ([__.6 (vector-set! vector.3 0 entry.1)]) vector.3)))))))
        (expose-allocation (add-types (sub (+ 1 (vector 1 2))))))))
