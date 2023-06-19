(ns pattern.r3.scanner
  (:require
   [pattern.types :refer [spliceable-pattern recombine]]
   [pattern.r3.core :refer [success success:env rebuild-rule]]
   [pattern.r3.rule :refer [unwrap unwrap-env]]
   [pattern.r3.combinators :refer [rule-list iterated rule-zipper]]
   [clojure.zip :as zip]))

(defmulti scanner* (fn [opts the-rule] (get-in (meta the-rule) [:rule :rule-type])))

(defn scanner
  ([the-rule] (scanner {} the-rule))
  ([opts the-rule] (scanner* opts the-rule)))


(defmethod scanner* :pattern/rule [{:keys [iterate lazy] :or {iterate true}} the-rule]
  ;; single rule approach:
  ;;'[??before rule1-body ??after]
  (let [m (:rule (meta the-rule))
        before (gensym 'before)
        segment (gensym 'segment)
        pattern (spliceable-pattern (:match m))
        after (gensym 'after)]
    (if pattern
      (cond->
          (rebuild-rule the-rule
            (list
              (symbol (str (if lazy "??!" "??") before))
              (list '?:as* segment pattern)
              (symbol (str "??" after)))
            `(when (seq ~segment)
               (when-let [body# ~(:src m)]
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
        iterate iterated)
      the-rule)))

(defn- merge-rules [opts r markers patterns handlers]
  (when (seq markers)
    (let [before (gensym 'before)
          segment (gensym 'segment)
          after (gensym 'after)
          pattern (list
                    (symbol (str (if (:lazy opts) "??!" "??") before))
                    (list '?:as* segment
                      (list* '| (map (fn [m p] (list '?:as* m p)) markers patterns)))
                    (symbol (str "??" after)))
          handlers `(cond ~@(mapcat vector markers handlers))]
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
                     env#))))))))))

 
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
        (if (= :pattern/rule (:rule-type m))
          (if-let [p (spliceable-pattern (:match m))]
            (recur children
              (or r child)
              (conj markers (gensym 'rule))
              (conj patterns p)
              (conj handlers (:src m))
              rules))
          (recur children nil [] [] []
            (-> rules
              (conj (merge-rules opts r markers patterns handlers))
              (conj (scanner opts child))))))
      (cond-> (rule-list (remove nil? (conj rules (merge-rules opts r markers patterns handlers))))
        iterate iterated))))

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

(comment

  (def r (scanner {:iterate false} (pattern/rule '[?a 1 ?b 2] [{a 1} {b 2}])))

  (def rl (rule-list
            (pattern/rule '[?a 1 ?b 9] nil #_[{a 1} {b 2}])
            (pattern/rule '[?a 1 ??_ ?b 2] [{a 1} '... {b 2}])
            (pattern/rule '[:x ?c 1] [c {:x 1}])))


  (def ro (pattern/in-order
            (pattern/rule '[?a 1 ?b 9] [{a 1} {b 2}])
            (pattern/rule '[?a 1 ??_ ?b 2] [{a 1} '... {b 2}])
            (pattern/rule '[:x ?c 1] [c {:x 1}])))


  (def rx (rule-list
            (pattern/rule '[?a 1 ?b 9] [{a 1} {b 2}])
            (pattern/rule '[?a 1 ??_ ?b 2] [{a 1} '... {b 2}])
            (pattern/in-order
              (pattern/rule '[:x ?c 1] [c {:x 1}])
              (pattern/rule '[:y ?c 1] [c {:y [c 1]}]))))


  (meta (scanner rx))

  (meta (scanner ro))

  (-> rl
    rule-zipper
    zip/node
    (= rl))

  (-> rl
    rule-zipper
    zip/down
    zip/right
    zip/right
    zip/right)

  (meta rl)

  (def srl (scanner rl))
  (srl '(1 2 3 4 :a 1 :b 9 :x :c 1 :d 2))

  (def sro (scanner ro))
  (sro '(1 2 3 4 :a 1 :b 2 :x :c 1 :d 2))

  (def srx (scanner rx))
  (sro '(1 2 3 4 :a 1 :b 2 :x :c 1 :d 2))


  ;; all other rules can be inverted:
  (scanner (in-order rule1 rule2)) #_-> (in-order (scanner rule1) (scanner rule2))
  (scanner (guard f rule)) #_-> (guard f (scanner rule))

  (scanner (rule-list rule0 rule1 (in-order rule2 rule3)))
  (rule-list (scanner-rule rule0 rule1) (in-order (scanner rule2) (scanner rule3)))


  (def odds (scanner {:lazy false :iterate false} (pattern/rule '(?? x odd?) (do (prn x) (when (next x) (apply + x))))))

  (odds '[2 3 1 6]))
