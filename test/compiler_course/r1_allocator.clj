(ns compiler-course.r1-allocator
  (:require [clojure.set :as set]
            [fermor.core :as f :refer [build-graph add-edges add-vertices both-e forked]]
            [fermor.core :as g]
            [matches :refer [on-subexpressions rule rule-list sub]]))

;; TODO: is rax ever looked at for liveness analysis? Not sure if I need this anyway...
(def register-synonyms {:al :rax})

(def move-instr? (into #{} '[movq movzbq]))
(def read-instr? (into #{} '[addq negq cmpq]))

(def liveness*
  (comp first
        (rule-list
         (rule '((? _ ~move-instr?) (v ?a) (v ?d))
               (let [live (-> (:live %env)
                              (disj d)
                              (conj a))]
                 (-> %env
                     (assoc :live live)
                     (update :i concat (map vector (repeat d) (disj live a d)))
                     (update :m conj [a d]))))
         (rule '((? _ ~move-instr?) ?_ (v ?d))
               (-> %env
                   (update :live disj d)
                   (update :i concat (map vector (repeat d) (disj (:live %env) d)))))
         (rule '((? _ ~move-instr?) (v ?a) ?_)
               (update %env :live conj a))
         (rule '((? _ ~read-instr?) (v ?a) (v ?d))
               (update %env :live conj a))
         (rule '((? _ ~read-instr?) ?_ (v ?a))
               (update %env :live conj a))
         (rule '((? _ ~read-instr?) (v ?a) ?_)
               (update %env :live conj a))
         (rule '((? _ ~read-instr?) (v ?a))
               (update %env :live conj a)))))

(def control-flow
  (rule-list
   (rule '(block ?label ?vars ??i* (jump ?a ?then) (jump ?b ?else))
         (sub [[?label ?then]
               [?label ?else]]))
   (rule '?_ [])))


(defn block-liveness [v init memo blocks]
  "In the book this is both 'uncover-live' and 'build-inter' plus the bonus exercise of building the move graph."
  (let [label (g/element-id v)]
    (if-let [live (@memo label)]
      live
      (let [b* (map (fn [v]
                      (block-liveness v init memo blocks))
                    (g/out v))
            live (reduce (fn [live b]
                           (-> live
                               (update :live into (:live b))
                               (update :blocks assoc (:label b) (dissoc b :blocks))
                               (update :blocks merge (:blocks b))))
                         init
                         b*)
            [_ label vars & i*] (get blocks label)]
        (let [live
              (reduce (fn [env i]
                        (liveness* i env
                                   (fn a [r _ _]
                                     [(update r :steps conj (:live r))
                                      nil])
                                   (fn b []
                                     [(update env :steps conj (:live env))
                                      nil])))
                      (assoc live :label label)
                      (reverse i*))]
          (swap! memo assoc label live)
          live)))))

(def liver*
  "In the book this is both 'uncover-live' and 'build-inter' plus the bonus exercise of building the move graph."
  (rule '(program ?vars ?blocks)
        (let [edges (mapcat control-flow (vals blocks))
              main (-> (build-graph)
                       (add-edges :to edges)
                       forked
                       (g/get-vertex 'start))
              main (block-liveness main
                                   {:i [] :m [] :steps () :live #{}}
                                   (atom {})
                                   blocks)
              liveness (assoc (:blocks main) 'start (dissoc main :blocks))]
          (reduce-kv (fn [liveness label block]
                       (assoc-in liveness [label :block] block))
                  liveness
                  blocks))))

(defn liveness [p]
  (liver* p))


(defn to-graph [liveness]
  (-> (build-graph)
      (add-edges :interference (mapcat :i (vals liveness)))
      (add-edges :move (mapcat :m (vals liveness)))
      (add-vertices (map (fn [v]
                           [v {:color nil}])
                         (reduce into (mapcat :steps (vals liveness)))))
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
