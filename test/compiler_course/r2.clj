(ns compiler-course.r2
  (:require [compiler-course.r1 :as r1]
            [fermor.core :as f :refer [build-graph add-edges add-vertices both-e forked]]
            [matches :refer [rule rule-list directed descend sub success on-subexpressions]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]))


#_ ;; example program
(program
 (x.1 x.2 tmp+.3)
 (movq (int 32) (v x.1))
 (movq (int 10) (v x.2))
 (movq (v x.2) (v tmp+.3))
 (addq (v x.1) (v tmp+.3))
 (movq (v tmp+.3) (reg rax))
 (retq))

(comment
  (-> (build-graph)
      (add-edges :x [['a 'b] ['a 'c]])
      forked
      f/all-vertices
      (->>
       (sort-by #(- (count (both-e [%])))))))

(def liveness*
  (rule-list
   (rule '(movq (v ?a) (v ?d))
         (let [live (-> (:live %env)
                        (disj d)
                        (conj a))]
           (-> %env
               (assoc :live live)
               (update :i concat (map vector (repeat d) (disj live a d)))
               (update :m conj [a d]))))
   (rule '(movq ?_ (v ?d))
         (-> %env
             (update :live disj d)
             (update :i concat (map vector (repeat d) (disj (:live %env) d)))))
   (rule '(movq (v ?a) ?_)
         (update %env :live conj a))
   ;; I think I can ignore negq. It reads and writes but it should never
   ;; change liveness?
   (rule '(addq (v ?a) (v ?d))
         (update %env :live conj a))
   (rule '(addq (v ?a) ?_)
         (update %env :live conj a))
   (rule '(addq ?_ (v ?d))
         %env)))

#_
(reduce (fn [env i]
          (first
           (liveness* i env
                      (fn a [a b c]
                        [(update a :steps conj (:live a))
                         b])
                      (fn b []
                        [(update env :steps conj (:live env))
                         nil]))))
        {:i [] :m [] :steps () :live #{}}
        (reverse
         '[(movq (int 1) (v v))
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
           (jmp conclusion)]))


(def liveness
  (rule '(program ?vars ??i*)
        (reduce (fn [env i]
                  (first
                   (liveness* i env
                              (fn a [r _ _]
                                [(update r :steps conj (:live r))
                                 nil])
                              (fn b []
                                [(update env :steps conj (:live env))
                                 nil]))))
                {:i [] :m [] :steps () :live #{}}
                (reverse i*))))

(defn to-graph [liveness]
  (-> (build-graph)
      (add-edges :interference (:i liveness))
      (add-edges :move (:m liveness))
      forked))

(defn interferedness [v]
  (count (both-e :interference v)))

(defn movedness [v]
  (count (both-e :move v)))

(let [g (to-graph
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
                    (jmp conclusion))))]
  (->> (f/all-vertices g)
       (sort-by (comp - movedness))
       (map (juxt identity movedness))))
