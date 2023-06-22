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
  "Convert any rule combinator to scan through a list or vector.

  The linear and iterate options are true by default.

  Linear scanner:

  It will do one full pass through the collection, but will not iterate at the
  top level.

  For linear scanner on a rule or rule-list, results from a matching rule are
  added to the final result and not rescanned. If you want to include the
  returned result in the data to scan again, set rescan to true.

  Not implemented yet: scanner on in-order combinator sets rescan to true by default.

  Rescanning scanner:

  Specified with the option {:linear false}.

  By default, :iterate is set, so the rule will iterate at the top level and
  rerun through the collection after each successful rule. If iterate is false,
  the scanner will terminate on the first match.

  Setting the :lazy option true will present the rules with the smallest
  possible matches first. Lazy rescanning scanner works from the back of the
  collection to the front."
  ([the-rule] (scanner* {} the-rule))
  ([{:keys [linear iterate lazy rescan] :or {linear true iterate true} :as opts} the-rule] (scanner* opts the-rule)))

(defn rule-handler [r]
  (let [handler-sym (gensym 'handler)
        m (:rule (meta r))]
    (-> m
      (select-keys [:src :handler-fn])
      (assoc
        :sym handler-sym
        :call `(~handler-sym ~(:handler-fn-args m))))))

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
        merged-handler (if one?
                         (:call (first handlers))
                         `(cond ~@(mapcat vector markers (map :call handlers))))]
    [pattern
     `(when (seq ~segment)
        (let [~'%env (assoc ~'%env :rule/datum ~segment)]
          (when-let [body# ~merged-handler]
            (let [env# (unwrap-env ~'%env body#)
                  body# (unwrap ::none body#)]
              (if (= ::none body#)
                (success:env env#)
                (let [body# (if (sequential? body#) body# [body#])]
                  (if (= ~segment body#)
                    (if (= ~'%env env#)
                      nil ;; rule failed
                      (success:env env#))
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
                      env#))))))))
     (mapv :sym handlers)
     (mapv :handler-fn handlers)]))

(defn- linear-body [opts markers patterns handlers]
  (let [complete (gensym 'complete)
        before (gensym 'before)
        segment (gensym 'segment)
        after (gensym 'after)
        one? (not (next patterns))
        pattern [(symbol (str "?" complete))
                 (list
                   (symbol (str "??" before))
                   (list '?:as* segment
                     (if one?
                       (first patterns)
                       (list* '| (map (fn [m p] (list '?:as* m p)) markers patterns))))
                   (symbol (str "??" after)))]
        ;; handlers is now a map
        merged-handler (if one?
                         (:call (first handlers))
                         `(cond ~@(mapcat vector markers (map :call handlers))))]
    [pattern
     `(when (seq ~segment)
        (let [~'%env (assoc ~'%env :rule/datum ~segment)]
          (when-let [success# ~merged-handler]
            (let [env# (unwrap-env ~'%env success#)
                  body# (unwrap ::none success#)]
              (if (= ::none body#)
                (success:env env#)
                (let [body# (if (sequential? body#) body# [body#])]
                  (if (= ~segment body#)
                    (if (= ~'%env env#)
                      nil ;; rule failed
                      (success:env env#))
                    (let [complete# (reduce conj! ~complete ~before)
                          complete# (reduce conj! complete# body#)]
                      (success
                        [complete# ~after]
                        env#)))))))))
     (mapv :sym handlers)
     (mapv :handler-fn handlers)]))

(defn- make-rule-rescanning [opts r markers patterns handlers]
  (when (seq patterns)
    (let [[pattern handler injection-names injection-data] (rescanning-body opts markers patterns handlers)]
      (cond-> (rebuild-rule r pattern handler injection-names injection-data)
        true (vary-meta assoc-in [:rule :scanner] true)
        (:iterate opts true) iterated))))

(defn- make-rule-linear
  [opts r markers patterns handlers]
  (when (seq patterns)
    (let [[pattern handler injection-names injection-data] (linear-body opts markers patterns handlers)]
      (in-order
        (-> (rule '(? v sequential?)
              [(transient []) (vec v)])
          raw
          (vary-meta assoc-in [:rule :scanner] true))
        (cond-> (rebuild-rule r pattern handler injection-names injection-data)
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

(defn- get-pattern [opts match]
  (let [pattern (spliceable-pattern match)]
    (if (and (seq? pattern) (= '?? (first pattern)) (= ::no (:lazy opts ::no)))
      (concat '(??!) (rest pattern))
      pattern)))

(defmethod scanner* :pattern/rule [opts the-rule]
  ;; single rule approach:
  ;;'[??before rule1-body ??after]
  (let [m (:rule (meta the-rule))
        pattern (get-pattern opts (:match m))]
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
          (if-let [p (get-pattern opts (:match m))]
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
