(ns pattern.r3.scanner
  (:require
   [pattern.types :refer [spliceable-pattern recombine]]
   [pattern.r3.core :refer [success success:env rebuild-rule rule pattern-args name-rule rule-fn-body raw-matches]]
   [pattern.r3.rule :refer [make-rule unwrap unwrap-env *post-processor*]]
   [pattern.r3.rewrite :refer [spliced]]
   [pattern.r3.combinators :refer [rule-list iterated rule-zipper in-order]]
   [pattern.r3.post-process :refer [raw]]
   [clojure.zip :as zip]))

(defmulti scanner* (fn [opts the-rule]
                    (get-in (meta the-rule) [:rule :rule-type])))

(defn scanner
  ([the-rule] (scanner* {} the-rule))
  ([opts the-rule] (scanner* opts the-rule)))

(defn rule-handler [r]
  (let [f (get-in (meta r) [:rule :handler])]
    `(~(f :handler) ~@(f :args))))

(defn- rescanning-body [opts markers patterns handlers]
  (let [before (gensym 'before)
        segment (gensym 'segment)
        one? (not (next patterns))
        after (gensym 'after)
        pattern (list
                  (symbol (str (if (:lazy opts) "??!" "??") before))
                  (list '?:as* segment
                    (if one?
                      (first patterns)
                      (list* '| (map (fn [m p] (list '?:as* m p)) markers patterns))))
                  (symbol (str "??" after)))
        handlers (if one?
                   (first handlers)
                   `(cond ~@(mapcat vector markers handlers)))]
    [pattern
     `(when (seq ~segment)
        (when-let [body# ~handlers]
          (let [env# (unwrap-env ~'%env body#)
                body# (unwrap ::none body#)]
            (if (= ::none body#)
              (success:env env#)
              (let [body# (if (sequential? body#) body# [body#])]
                (success
                  (if (seq ~before)
                    (if (seq body#)
                      (into ~before (concat body# ~after))
                      (into ~before ~after))
                    (if (seq ~after)
                      (if (vector? body#)
                        (into body# ~after)
                        (vec (concat body# ~after)))
                      (vec body#)))
                  env#))))))]))

(defn- linear-body [opts markers patterns handlers]
  (let [complete (gensym 'complete)
        before (gensym 'before)
        segment (gensym 'segment)
        after (gensym 'after)
        one? (not (next patterns))
        pattern [(symbol (str "?" complete))
                 (list
                   (symbol (str (if (:lazy opts) "??!" "??") before))
                   (list '?:as* segment
                     (if one?
                       (first patterns)
                       (list* '| (map (fn [m p] (list '?:as* m p)) markers patterns))))
                   (symbol (str "??" after)))]
        handlers (if one?
                   (first handlers)
                   `(cond ~@(mapcat vector markers handlers)))]
    [pattern
     `(when (seq ~segment)
        (when-let [success# ~handlers]
          (let [env# (unwrap-env ~'%env success#)
                body# (unwrap ::none success#)]
            (if (= ::none body#)
              (success:env env#)
              (let [complete# (reduce conj! ~complete ~before)
                    complete# (reduce conj! complete# (if (sequential? body#) body# [body#]))]
                (success
                  [complete# ~after]
                  env#))))))]))

(defn- make-rule-rescanning
  ([opts r markers patterns handlers]
   (when (seq patterns)
     (let [[pattern handler] (rescanning-body opts markers patterns handlers)]
       (cond-> (rebuild-rule r pattern handler)
         true (vary-meta assoc-in [:rule :scanner] true)
         (:iterate opts true) iterated)))))

(defn- make-rule-linear
  [opts r markers patterns handlers]
  (when (seq patterns)
    (let [[pattern handler] (linear-body opts markers patterns handlers)]
      (in-order
        (-> (rule '(? v sequential?)
              [(transient []) (vec v)])
          raw
          (vary-meta assoc-in [:rule :scanner] true))
        (cond-> (rebuild-rule r pattern handler)
          true (vary-meta assoc-in [:rule :scanner] true)
          (:iterate opts true) iterated)
        (-> (rule '[?result ?remainder]
              (success
                (if (= ::not-found (get result 0 ::not-found))
                  remainder
                  (persistent! (reduce conj! result remainder)))
                (dissoc %env :rule/datum)))
          raw
          (vary-meta assoc-in [:rule :scanner] true))))))


(defn- make-scanner-rule
  ([opts r pattern handler]
   (make-scanner-rule opts r nil [pattern] [handler]))
  ([opts r markers patterns handlers]
   (if (:linear opts (:iterate opts true))
     (make-rule-linear opts r markers patterns handlers)
     (make-rule-rescanning opts r markers patterns handlers))))

(defmethod scanner* :pattern/rule [{:keys [iterate lazy] :or {iterate true} :as opts} the-rule]
  ;; single rule approach:
  ;;'[??before rule1-body ??after]
  (let [m (:rule (meta the-rule))
        pattern (spliceable-pattern (:match m))]
    (if (:scanner m)
      the-rule
      (if pattern
        (make-scanner-rule opts the-rule pattern (rule-handler the-rule))
        the-rule))))

 
(defmethod scanner* :pattern.r3.combinators/rule-list [{:keys [iterate] :or {iterate true} :as opts} the-rule]
  ;; rule-list approach
  ;; '[??before (| (?:as* rule1 rule1-body) (?:as* rule2 rule2-body) ... (?:as* rule-n rule-n-body)) ??after]
  (loop [[child & children] (zip/children (rule-zipper the-rule))
         r nil
         markers []
         patterns []
         handlers []
         rules []]
    (if child
      (let [m (:rule (meta child))]
        (if (and (= :pattern/rule (:rule-type m)) (not (:scanner m)))
          (if-let [p (spliceable-pattern (:match m))]
            (recur children
              (or r child)
              (conj markers (gensym 'rule))
              (conj patterns p)
              (conj handlers (rule-handler child))
              rules))
          (recur children nil [] [] []
            (-> rules
              (conj (make-scanner-rule opts r markers patterns handlers))
              (conj (scanner* opts child))))))
      ;; Don't be linear or iterate on sub-rules if there are multiple rules in the rule-list
      (let [rule-opts (if (seq rules)
                        (assoc opts :linear false :iterate false)
                        opts)
            rule (make-scanner-rule rule-opts r markers patterns handlers)
            rules (conj rules rule)]
        (cond-> (rule-list (remove nil? rules))
          iterate iterated)))))

(defmethod scanner* :default [opts the-rule]
  ;; all other rules can be inverted:
  ;; (scanner (in-order rule1 rule2)) #_-> (in-order (scanner rule1) (scanner rule2))
  ;; (scanner (guard f rule)) #_-> (guard f (scanner rule))

  ;;      (scanner (rule-list rule0 rule1 (in-order rule2 rule3)))
  ;; #_-> (rule-list (rule rule0+rule1) (in-order (scanner rule2) (scanner rule3)))

  (loop [z (zip/down (rule-zipper the-rule))
         rules []]
    (if z
      (recur (zip/right z) (conj rules (scanner* opts (zip/node z))))
      (recombine the-rule rules))))

#_
(defmacro scan-rule
  "Create a specialized rule variant that scans through a collection and
  replaces matching sequences with new sequences.

  The pattern must be a vector, which may match any number of items. The

  This example matches exactly 2 identical items and replaces them with one:

         ((scan-rule minimal-example ^{:iterate false}
            '[?a ?a]
            [a])
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 3 4 4]

  The result is not rescanned, resulting in 3 to appear twice after matching
  since the third appearance is solo after the first pair has been transformed.

         ((scan-rule typical-example
            '[?a ?a]
            [a])
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 4]

  The rule moves monotonically forward through the list without
  rescanning of the previously matched list that typically happens with a
  simpler rule such as the following:

         ((iterated
            (rule iterating-example
              '[??before ?a ?a ??after]
              (sub [??before ?a ??after])))
          [1 2 2 3 3 3 4 4 4 4])
         ;; => [1 2 3 4]

  If you want that behavior, you can do this:

         (scan-rule x ^{:linear false} '[?a ?a] [a])"
  ([pattern body]
   `(scan-rule nil ~pattern ~body))
  ([name pattern handler]
   (when-not (:no-assert (meta pattern))
     (assert (vector? (second pattern)) "Pattern must be a vector"))
   (let [opts (meta pattern)
         pattern (list* '?:1 (second pattern))]
     (if (and (:linear opts true) (:iterate opts true))
       (let [[pattern handler] (linear-body opts nil [pattern] [handler])]
         `(in-order
            (-> (raw (rule '~'(? v sequential?) [(transient []) (vec ~'v)]))
              (vary-meta assoc-in [:rule :scanner] true))
            (in-order
              (iterated
                (cond->>
                    (make-rule ~(spliced `'~pattern)
                      (rule-fn-body ~@(when name [name])
                        ~(pattern-args pattern)
                        ~(:env-args opts)
                        ~handler)
                      raw-matches
                      *post-processor*
                      {:may-call-success0? false
                       :src '~handler
                       :pattern-meta '~opts
                       :scanner true})
                  ~(boolean name) (name-rule '~name)))
              (raw
                (->
                  (rule '~'[?result ?remainder]
                    (success
                      (if (= ::not-found (get ~'result 0 ::not-found))
                        ~'remainder
                        (persistent!
                          (if (seq ~'remainder)
                            (reduce conj! ~'result ~'remainder)
                            ~'result)))
                      (dissoc ~'%env :rule/datum)))
                  (vary-meta assoc-in [:rule :scanner] true))))))
       (let [[pattern handler] (rescanning-body opts nil [pattern] [handler])
             form `(cond->>
                       (make-rule ~(spliced `'~pattern)
                         (rule-fn-body ~@(when name [name])
                           ~(pattern-args pattern)
                           ~(:env-args opts)
                           ~handler)
                         raw-matches
                         *post-processor*
                         {:may-call-success0? false
                          :src '~handler
                          :pattern-meta '~opts
                          :scanner true})
                     ~(boolean name) (name-rule '~name))]
         (if (:iterate opts true) `(iterated ~form) form))))))
