(ns compiler-course.pass09-explicate-control
  (:require
   [matches :refer [=> dialects directed gennice rule rule-list sub]]))


;; Explicate expressions: remove nesting (aka flatten)

(declare x-pred x-assign)

(let [x-assign*
      (dialects
       (=> Simplified Explicit)
       (rule-list
        (rule '(if ?e ?then ?else)
              (let [then (x-assign (:var %env) then (:cont %env))
                    else (x-assign (:var %env) else (:cont %env))]
                (x-pred e then else)))
        (rule '((?:= let) ([?v ?e]) ?body)
              (let [body (x-assign (:var %env) body (:cont %env))]
                (x-assign v e body)))
        (rule '?value (-> (:cont %env)
                          (update :s (fn [s] (into [(sub (assign ~(:var %env) ?value))] s)))
                          (update :v (fnil conj #{}) (:var %env))))))]
  (defn x-assign [v exp cont]
    (first (x-assign* exp {:var v :cont cont}))))

(defn pred-block [{:keys [then else]} f]
  (let [then (assoc then :label (gennice 'then))
        else (assoc else :label (gennice 'else))]
    {:v (into (:v then) (:v else))
     :b (merge {(:label then) (dissoc then :b)
                (:label else) (dissoc else :b)}
               (:b then)
               (:b else))
     :s (f (:label then) (:label else))}))

(let [x-pred*
      (dialects
       (=> Simplified Explicit)
       (rule-list
        (rule '(if ?e ?then ?else)
              (let [then (x-pred then (:then %env) (:else %env))
                    else (x-pred else (:then %env) (:else %env))]
                (x-pred e then else)))
        (rule '(not ?e)
              (x-pred e (:else %env) (:then %env)))
        (rule true (:then %env))
        (rule false (:else %env))
        (rule '((?:= let) ([?v ?e]) ?body)
              (let [body (x-pred body (:then %env) (:else %env))]
                (x-assign v e body)))
        (rule '(??items)
              (pred-block %env #(sub [(if (??items) (goto ~%1) (goto ~%2))])))
        (rule '?other
              (x-pred (sub (eq? ?other true)) (:then %env) (:else %env)))))]
  (defn x-pred [exp then else]
    (first (x-pred* exp {:then then :else else}))))

(def x-tail
  (dialects
   (=> Simplified Explicit)
   (rule-list
    (rule '(if ?e ?then ?else)
          (let [then (x-tail then)
                else (x-tail else)]
            (x-pred e then else)))
    (rule '((?:= let) ([?v ?e]) ?body)
          (let [body (x-tail body)]
            (x-assign v e body)))
    (rule '(call ?v ??e:args)
          {:s [(sub (tailcall ?v ??args))]})
    (rule '?other {:s [(sub (return ?other))]}))))

(def explicate-control
  (dialects
   (=> Simplified Explicit)
   (directed
    (rule-list
     (rule '(program ??->define*))
     (rule '(define (?v ??arg*) ?type ?e)
           (let [e (x-tail e)
                 start (symbol (str v "-start"))
                 blocks (reduce-kv (fn [blocks l b]
                                     (assoc blocks l
                                            (sub (block ?l
                                                        ~@(:s b)))))
                                   {} (assoc (:b e) start (assoc e :label start)))]
             (sub (define [?v [??arg*] ?type] [~@(:v e)] ~blocks))))))))
