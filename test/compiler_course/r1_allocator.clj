(ns compiler-course.r1-allocator
  (:require [clojure.set :as set]
            [fermor.core :as f :refer [build-graph add-edges add-vertices both-e forked]]
            [fermor.core :as g]
            [matches :refer [on-subexpressions rule rule-list sub matcher compile-pattern success
                             dialects =>]]))

(def registers '[rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14])
(def register-indices (into {} (map vector registers (range 20))))
(def caller-saved-registers (into #{} '[rax rcx rdx rsi rdi r8 r9 r10 r11]))
(def callee-saved-registers (into #{} '[rsp rbp rbx r12 r13 r14 r15]))

;; TODO: is rax ever looked at for liveness analysis? Not sure if I need this anyway...
(def register-synonyms {:al :rax})

(def move-instr? (into #{} '[movq movzbq leaq]))
(def read-instr? (into #{} '[addq negq cmpq]))

(def heap? (matcher '(Vector ??types)))
(def reg? (matcher '(reg ?name)))

(def liveness*
  "Capture currently-live variables in :live plus aggregate (as a collection of
  edge pairs) both interference in :i and the move graph in :m"
  (dialects
   (=> Selected nil)
   (comp first
         (rule-list
          (rule '((? _ ~move-instr?) (v ?v:a) (v ?v:d))
                (let [live (-> (:live %env)
                               (disj d)
                               (conj a))]
                  (-> %env
                      (assoc :live live)
                      (update :i concat (map vector (repeat d) (disj live a d)))
                      (update :m conj [a d]))))
          (rule '((? _ ~move-instr?) ?_ (v ?v:d))
                (-> %env
                    (update :live disj d)
                    (update :i concat (map vector (repeat d) (disj (:live %env) d)))))
          (rule '(callq ?lbl)
                ;; A call to collect interferes with heap pointers in all registers
                (let [regs caller-saved-registers
                      all-regs (map #(sub (reg ~%))
                                    (concat regs
                                            (when (= 'collect lbl)
                                              callee-saved-registers)))
                      regs (map #(sub (reg ~%)) regs)
                      edges (for [v (:live %env)
                                  :let [regs (if (heap? (get-in %env [:types v]))
                                               all-regs
                                               regs)]
                                  reg regs]
                              [v reg])]
                  (update %env :i concat edges)))
          (rule '((| indirect-callq tailjmp) (v ?x))
                ;; TODO: I something like callq here, interfering all over the place.
                (update %env :live conj x))
          (rule '((? _ ~move-instr?) (v ?v:a) ?_)
                (update %env :live conj a))
          (rule '((? _ ~read-instr?) (v ?v:a) (v ?v:d))
                (update %env :live conj a d))
          (rule '((? _ ~read-instr?) ?_ (v ?v:a))
                (update %env :live conj a))
          (rule '((? _ ~read-instr?) (v ?v:a) ?_)
                (update %env :live conj a))
          (rule '((? _ ~read-instr?) (v ?v:a))
                (update %env :live conj a))))))

(def control-flow
  (dialects
   (=> Selected nil)
   (rule-list
    (rule '(block ?lbl ??stmt* (jump ?a ?then) (jump ?b ?else))
          (sub [[?lbl ?then]
                [?lbl ?else]]))
    (rule '?_ []))))

(defn block-liveness
  "In the book this is both 'uncover-live' and 'build-inter' plus the bonus
  exercise of building the move graph."
  [v init memo blocks]
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
            [_ label & i*] (get blocks label)]
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

;; Caller saved registers "already" interfere with "call-live vector-typed
;; variables".  I think call-live means ones live at the time of the call. That
;; is because all registers that must be saved before calling interfere with
;; making a call.
;; - To force vector-typed vars to *all* be spilled from registers,
;;   I must just make them interfere specifically with the call to collect as
;;   well.
;; - The book recommends I do this by adding interference to *registers* but
;;   the intf graph is to *vars*. How do add interf to registers??
;;
;; That way when I collect, no vectors will be in registers, and this is
;; accomplished just by allocating registers such that it falls out that way --
;; it doesn't mean that calling collect causes a bunch of new activity, but
;; rather that if a vector is being allocated (triggering possible collect),
;; other vectors are going to be pre-allocated outside of registers.
;; - I will have to do something to force those allocations to be to the heap
;;   rather than the stack.

(def fn-liveness*
  "In the book this is both 'uncover-live' and 'build-inter' plus the bonus
  exercise of building the move graph."
  (dialects
   (=> Selected nil)
   (rule '(define ?v ?var-types ?blocks)
         (let [edges (mapcat control-flow (vals blocks))
               start (symbol (str v '-start))
               main (-> (build-graph)
                        (add-edges :to edges)
                        forked
                        (g/get-vertex start))
               main (block-liveness main
                                    {:i [] :m [] :steps () :live #{} :types var-types}
                                    (atom {})
                                    blocks)
               liveness (assoc (:blocks main) start (dissoc main :blocks))]
           (reduce-kv (fn [liveness label block]
                        (assoc-in liveness [label :block] block))
                      liveness
                      blocks)))))

(defn liveness
  {:=>/from 'Selected}
  [p]
  (fn-liveness* p))

(defn to-graph [liveness]
  (-> (build-graph)
      (add-edges :interference (mapcat :i (vals liveness)))
      (add-edges :move (mapcat :m (vals liveness)))
      (add-vertices (map (fn [v]
                           [v {:color nil}])
                         (reduce into (mapcat :steps (vals liveness)))))
      forked))

(defn set-color
  "Update graph vertex with :color attr"
  [g v color]
  (let [doc (f/get-document (if (f/vertex? v)
                              v
                              (f/get-vertex g v)))]
    (f/set-document g v (assoc doc :color color))))

(defn color [v]
  (:color (f/get-document v)))

(defn interference [v]
  (set (keep (fn [v]
               (let [id (f/element-id v)]
                 ;; If a register is added to the inferference graph, it just means that
                 ;; the register interferes with whatever it's linked to.
                 (if-let [[reg] (reg? id)]
                   (register-indices reg) ;;
                   (color v))))
             (f/both :interference v))))

(defn biased-reg [v interf]
  (first
   (set/difference (set (keep color (f/both :move v)))
                   interf)))

(defn saturation [v]
  (- (count (interference v))))

(defn movedness [v]
  (- (count (both-e :move v))))

(defn order [v]
  (+ (* 1024 (saturation v))
     (movedness v)))

(defn next-color
  "Provide the lowest-indexed free register from the registers vector"
  [v]
  (let [interference (interference v)
        free (biased-reg v interference)]
    (or free
        (first (remove interference (range 1000))))))

(defn allocate-registers* [g]
  (loop [g g]
    (if-let [v (->> (f/all-vertices g)
                    (remove (comp reg? f/element-id))
                    (remove color)
                    (sort-by order)
                    first)]
      (recur (set-color g (f/element-id v) (next-color v)))
      g)))

(defn get-location [t n]
  (if-let [reg (nth registers n nil)]
    (sub (reg ?reg))
    ;; NOTE this uses a naive algo that allocates both heap and stack for every
    ;; spilled var which I think simplifies the color selection step
    (if (heap? t)
      (sub (heap ~(- n (count registers))))
      (sub (stack ~(- n (count registers)))))))

(defn var-locations [types g]
  (into {}
        (keep (fn [v]
                (let [var (f/element-id v)]
                  (when-not (reg? var)
                    [var
                     (get-location (types var) (color v))])))
              (f/all-vertices g))))

(def with-allocated-registers
  (comp first
        (on-subexpressions (rule '(v ?v) (get-in %env [:loc v])))))
