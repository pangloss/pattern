(ns pattern.matchers.map
  "Matchers defined in this namespace are not available during bootstrap.

  Because of that, they do have access to all of the features of the library."
  (:refer-clojure :exclude [trampoline])
  (:require [genera :refer [trampoline trampolining bouncing defgen=]]
            [uncomplicate.fluokitten.core :as f]
            [pattern.types :refer [spliceable-pattern]]
            [pattern.match.core :as m :refer :all]
            [pattern.match.predicator :refer [var-abbr]]
            [pattern.r3.rewrite :refer [spliced]]
            [clojure.set :as set])
  (:import (pattern.types Env)))

(set! *warn-on-reflection* true)

(defn- match-map-intersection
  [[_ map-literal remainder :as pattern] comp-env]
  (let [map-keys (vec (keys map-literal))]
    (vary-meta
      (compile-pattern*
        (list* '&
          map?
          (fn check-map-intersection [x] (= map-literal (select-keys x map-keys)))
          (when remainder
            [(list '?:chain '?_ (fn dissoc-known [x] (apply dissoc x map-keys))
               remainder)]))
        comp-env)
      assoc :expanded pattern)))

(defn match-map-literal [the-map comp-env]
  (let [kv->literals
        (reduce (fn [m kv] (assoc m kv
                            [(:literal (meta (compile-pattern* (key kv) comp-env)))
                             (:literal (meta (compile-pattern* (val kv) comp-env)))]))
          {} the-map)
        patterns (keep #(let [[kl vl] (kv->literals %)]
                          (when-not (and kl vl) %))
                   the-map)
        grouped-literals (keep #(let [[kl vl] (kv->literals %)]
                                  (when (and kl vl) (vec (concat kl vl))))
                           the-map)
        closed? (:closed? comp-env)
        literals (when (seq grouped-literals)
                   (let [literal-map (into {} grouped-literals)]
                     (if (and closed? (not (seq patterns)))
                       (list '?:= literal-map)
                       (list '?:map-intersection literal-map))))
        patterns (when (seq patterns)
                   (->> patterns
                     (sort-by (fn [[k _ :as kv]]
                                (cond (var-name k) 1  ;; may be bound
                                      (first (kv->literals kv)) 0 ;; has a key literal
                                      (second (kv->literals kv)) 2 ;; has a val literal
                                      :else 3))) ;; no literal
                     reverse
                     (reduce (fn [m [k v]] (list '?:map-kv k v m)) nil)))]
    (compile-pattern*
      (if literals
        (if (seq patterns)
          (concat literals [patterns])
          literals)
        (if patterns
          patterns
          (if closed?
            (list '?:= {})
            map?)))
      comp-env)))

(defn- match-map-kv
  [[_ key-pattern value-pattern remainder :as pattern] comp-env]
  (let [key-matcher (compile-pattern* key-pattern comp-env)
        key-var (var-name key-pattern)
        literal-key (:literal (meta key-matcher))
        value-matcher (compile-pattern* value-pattern comp-env)
        literal-value (:literal (meta value-matcher))
        literal (when (and literal-key literal-value) (into literal-key literal-value))
        closed? (:closed? comp-env)
        remainder-matcher (when remainder (compile-pattern* remainder comp-env))]
    (if (and literal closed? (or (not remainder) (:literal (meta remainder-matcher))))
      (let [base (or (first (:literal (meta remainder-matcher))) {})]
        (compile-pattern* (list '?:literal (conj base literal)) comp-env))
      (letfn [(->key-bound [kv dictionary env]
                (let [bound (get dictionary key-var)
                      k (if bound (:value bound) (key kv))]
                  (key-matcher [k] dictionary env)))
              (->key [kv dictionary env] (key-matcher [(key kv)] dictionary env))
              (->val [kv dictionary env] (value-matcher [(val kv)] dictionary env))
              (on-direct-lookup [kv the-map dictionary ^Env env]
                (if-let [result
                         (value-matcher [(val kv)] dictionary
                           (assoc env :succeed
                             (fn match2-succeed [new-dictionary n]
                               (let [remaining-map (dissoc the-map (key kv))]
                                 (if remainder-matcher
                                   (remainder-matcher [remaining-map] new-dictionary env)
                                   (if (and closed? (seq remaining-map))
                                     (on-failure :closed pattern new-dictionary env 1
                                       remaining-map kv)
                                     ((.succeed env) new-dictionary 1)))))))]
                  result
                  (on-failure :no-val-match pattern dictionary env 1
                    the-map (or (first literal-key) (:value (get dictionary key-var))))))
              (scan-lookup-step [kv before after dictionary ^Env env matcher1 matcher2 retry]
                (if kv
                  (let [after (dissoc after (key kv))]
                    ;; if val is literal match it first, otherwise always match on key first
                    (if-let [result
                             (matcher1 kv dictionary
                               (assoc env :succeed
                                 (fn match1-succeed [new-dictionary n]
                                   (matcher2 kv new-dictionary
                                     (assoc env :succeed
                                       (fn match2-succeed [new-dictionary n]
                                         (if remainder-matcher
                                           (remainder-matcher [(into after before)] new-dictionary env)
                                           (if (and closed? (or (seq before) (seq after)))
                                             (on-failure :closed pattern new-dictionary env 1
                                               (into after before) kv :retry retry)
                                             ((.succeed env) new-dictionary 1)))))))))]
                      result
                      (retry (conj before kv) after)))
                  (on-failure :not-found pattern dictionary env 1 (into after before) nil :retry retry)))]
        (let [[matcher1 matcher2] (if (and literal-value (not key-var))
                                    [->val ->key]
                                    [->key ->val])]
          (with-meta
            (cond literal-key
                  (fn map-kv-matcher [data dictionary ^Env env]
                    (if (seq data)
                      (letfn [(map-key-matcher [the-map]
                                (if-let [kv (find the-map (first literal-key))]
                                  (on-direct-lookup kv the-map dictionary env)
                                  (on-failure :not-found pattern dictionary env 1
                                    the-map (or (first literal-key) (:value (get dictionary key-var))))))]
                        (let [the-map (first data)]
                          (if (and (map? the-map) (not (record? the-map)))
                            (if (seq the-map)
                              (map-key-matcher the-map)
                              (on-failure :mismatch pattern dictionary env 1 data the-map))
                            (on-failure :type pattern dictionary env 1 data the-map))))
                      (on-failure :missing pattern dictionary env 0 data nil)))
                  key-var
                  (fn map-kv-matcher [data dictionary ^Env env]
                    (if (seq data)
                      (letfn [(map-kv-item-lookup [the-map]
                                (if-let [bound (get dictionary key-var)]
                                  (if-let [kv (find the-map (get bound :value))]
                                    (on-direct-lookup kv the-map dictionary env)
                                    (on-failure :not-found pattern dictionary env 1 the-map (:value bound) :retry retry))
                                  (trampoline retry [] the-map)))
                              (map-kv-item-matcher [before after dictionary]
                                (scan-lookup-step (first after) before after dictionary env matcher1 matcher2 retry))
                              (retry [scanned-map remaining-map]
                                (if (seq remaining-map)
                                  (bouncing (map-kv-item-matcher scanned-map remaining-map dictionary))
                                  (on-failure :mismatch pattern dictionary env 1 data remaining-map :retry retry)))]
                        (let [the-map (first data)]
                          (if (and (map? the-map) (not (record? the-map)))
                            (map-kv-item-lookup the-map)
                            (on-failure :type pattern dictionary env 1 data the-map :retry retry))))
                      (on-failure :missing pattern dictionary env 0 data nil)))
                  :else
                  (fn map-kv-matcher [data dictionary ^Env env]
                    (if (seq data)
                      (letfn [(map-kv-item-matcher [before after dictionary]
                                (let [kv (if literal-value
                                           ;; do a fast scan for a matching literal
                                           (loop [before before after after kv (first after)]
                                             (when kv
                                               (if (= (first literal-value) (val kv))
                                                 [before after kv]
                                                 (let [after (dissoc after (key kv))]
                                                   (recur (conj before kv) after (first after))))))
                                           [before after (first after)])
                                      [before after kv] (if (map-entry? kv) [before after kv] kv)]
                                  (scan-lookup-step kv before after dictionary env matcher1 matcher2 retry)))
                              (retry [scanned-map remaining-map]
                                (if (seq remaining-map)
                                  (bouncing (map-kv-item-matcher scanned-map remaining-map dictionary))
                                  (on-failure :mismatch pattern dictionary env 1 data remaining-map :retry retry)))]
                        (let [the-map (first data)]
                          (if (and (map? the-map) (not (record? the-map)))
                            (trampoline retry [] the-map)
                            (on-failure :type pattern dictionary env 1 data the-map :retry retry))))
                      (on-failure :missing pattern dictionary env 0 data nil))))
            (merge (merge-meta (map meta [key-matcher value-matcher remainder-matcher]))
              {:length (len 1)
               `spliceable-pattern (fn [_] pattern)
               :expanded pattern})))))))


(register-matcher '?:map-kv #'match-map-kv)
(register-matcher '?:map-intersection #'match-map-intersection)
(defgen= matcher-type [(every-pred map? (complement record?))] :map)
(register-matcher :map #'match-map-literal)
