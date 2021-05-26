(ns compiler-course.r1-allocator
  (:require [compiler-course.r1 :as r1]
            [fermor.core :as f :refer [build-graph add-edges add-vertices both-e forked]]
            [matches :refer [rule rule-list directed descend sub success on-subexpressions]]
            [matches.nanopass.pass :refer [defpass let-rulefn]]
            [clojure.set :as set]))

(def liveness*
  (comp first
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
         (rule '(addq (v ?a) (v ?d))
               (update %env :live conj a))
         (rule '(addq (v ?a) ?_)
               (update %env :live conj a)))))

(def liveness
  "In the book this is both 'uncover-live' and 'build-inter' plus the bonus exercise of building the move graph."
  (rule '(program ?vars ??i*)
        (reduce (fn [env i]
                  (liveness* i env
                             (fn a [r _ _]
                               [(update r :steps conj (:live r))
                                nil])
                             (fn b []
                               [(update env :steps conj (:live env))
                                nil])))
                {:i [] :m [] :steps () :live #{}}
                (reverse i*))))

(defn to-graph [liveness]
  (-> (build-graph)
      (add-edges :interference (:i liveness))
      (add-edges :move (:m liveness))
      (add-vertices (map (fn [v]
                           [v {:color nil}])
                         (reduce into (:steps liveness))))
      forked))

(defn set-color [g v color]
  (f/set-document g v (assoc (f/get-document (if (f/vertex? v) v(f/get-vertex g v))) :color color)))

(defn color [v]
  (:color (f/get-document v)))

(defn interference [v]
  (set (keep color (f/both :interference v))))

(defn biased-reg [v interf]
  (first
   (set/difference (set (keep color (f/both :move v)))
                   interf)))

(defn saturation [v]
  (- (count (interference v))))

(defn movedness [v]
  (- (count (both-e :move v))))

(defn order [v]
  (+ (* 100 (saturation v))
     (movedness v)))

(defn next-color [v]
  (let [interference (interference v)
        free (biased-reg v interference)]
    (or free
        (first (remove interference (range 100))))))

(defn allocate-registers* [g]
  (loop [g g]
    (if-let [v (->> (f/all-vertices g)
                    (remove color)
                    (sort-by order)
                    first)]
      (recur (set-color g (f/element-id v) (next-color v)))
      g)))

(def registers '[rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14])

(defn get-location [n]
  (if-let [reg (nth registers n nil)]
    (sub (reg ?reg))
    (sub (stack ~(- n (count registers))))))

(defn var-locations [g]
  (into {}
        (map (fn [v]
               [(f/element-id v)
                (get-location (color v))])
             (f/all-vertices g))))

(def with-allocated-registers
  (comp first
        (on-subexpressions (rule '(v ?v) (get-in %env [:loc v])))))

(def with-stack-size
  (comp first
        (rule '(program ??etc) (sub (program ~(:stack-size %env) ??etc)))))

(defn allocate-registers [prog]
  (let [g (to-graph (liveness prog))
        g (allocate-registers* g)
        stack-size (->> (vals (var-locations g))
                        (filter #(= 'stack (first %)))
                        (map second)
                        (apply max 0)
                        r1/stack-size)]
    (-> prog
        (with-allocated-registers {:loc (var-locations g)})
        (with-stack-size {:stack-size stack-size}))))

(def patch-instructions
  (directed (rule-list (rule '(program ?size ?vars ??->i*)
                             (sub (program ?size ?vars ~@(apply concat i*))))
                       (rule '(movq ?a ?a) [])
                       (rule '?x [x]))))

(def asfu (comp #'allocate-registers #'r1/sfu))
(def pasfu (comp #'patch-instructions #'asfu))
(def spasfu (comp println #'r1/stringify #'pasfu))
