(ns pattern.r3.scanner
  (:require
   [pattern.types :refer [spliceable-pattern recombine]]
   [pattern.r3.core :refer [success success:env rebuild-rule rule]]
   [pattern.r3.rule :refer [unwrap unwrap-env]]
   [pattern.r3.combinators :refer [rule-list iterated rule-zipper in-order]]
   [pattern.r3.post-process :refer [raw]]
   [clojure.zip :as zip]))

(defmulti scanner* (fn [opts the-rule] (get-in (meta the-rule) [:rule :rule-type])))

(defn scanner
  ([the-rule] (scanner {} the-rule))
  ([opts the-rule] (scanner* opts the-rule)))

(defn- make-rule-rescanning
  ([opts r markers patterns handlers]
   (when (seq patterns)
     (let [before (gensym 'before)
           segment (gensym 'segment)
           one? (= 1 (count patterns))
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
       (cond->
           (rebuild-rule r
             pattern
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
                          env#)))))))
         true (vary-meta assoc-in [:rule :scanner] true)
         (:iterate opts true) iterated)))))

(defn- make-rule-linear
  [opts r markers patterns handlers]
  (when (seq patterns)
    (let [complete (gensym 'complete)
          before (gensym 'before)
          segment (gensym 'segment)
          one? (= 1 (count patterns))
          after (gensym 'after)
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
      (in-order
        (-> (rule '(? v sequential?)
              [(transient []) (vec v)])
          raw
          (vary-meta assoc-in [:rule :scanner] true))
        (-> (rebuild-rule r
              pattern
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
                           env#)))))))
          (vary-meta assoc-in [:rule :scanner] true)
          iterated)
        (-> (rule '[?result ?remainder]
              (if (= ::not-found (get result 0 ::not-found))
                remainder
                (persistent! (reduce conj! result remainder))))
          raw
          (vary-meta assoc-in [:rule :scanner] true))))))


(defn- make-rule
  ([opts r pattern handler]
   (make-rule opts r nil [pattern] [handler]))
  ([opts r markers patterns handlers]
   (if (and (:linear opts) (:iterated opts true))
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
        (make-rule opts the-rule pattern (:src m))
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
              (conj handlers (:src m))
              rules))
          (recur children nil [] [] []
            (-> rules
              (conj (make-rule opts r markers patterns handlers))
              (conj (scanner opts child))))))
      ;; Don't be linear or iterate on sub-rules if there are multiple rules in the rule-list
      (let [rule-opts (if (seq rules)
                        (assoc opts :linear false :iterate false)
                        opts)
            rule (make-rule rule-opts r markers patterns handlers)
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
