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
          '(? _ map?)
          (list '? '_ (fn check-map-intersection [x] (= map-literal (select-keys x map-keys))))
          (when remainder
            [(list '?:chain '?_ (fn dissoc-known [x] (apply dissoc x map-keys))
               remainder)]))
        comp-env)
      assoc :expanded pattern)))

(defn match-map-literal [the-map comp-env]
  (let [kv->literals
        (reduce (fn [m [k v :as kv]]
                  (assoc m kv
                    [(:literal (meta (compile-pattern* k comp-env)))
                     (:literal (meta (compile-pattern* v comp-env)))]))
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
            '(?:= {})
            '(? _ map?))))
      comp-env)))

(defn match-map
  "Match map datastructures. For instance to match {:from 1 :to 10}:

      (?:map :from ?f :to ?t)

  These would both work identically because the matcher will do some simple
  organization of the terms to try to maximize efficiency:

     (?:map :addr ?addr ?addr ?info)
     (?:map ?addr ?info :addr ?addr)

  If the pattern contains multiple keys meant to match the same key of the map,
  it will never match because after a key is matched, it is removed from the
  map matched by the next key/value matcher pair. Use `&` and `|` in either key
  or value position to apply multiple patterns to a single data key or value.

  This matcher does not fail if there are extra keys in the map it's matching
  against unless you wrap them in ?:closed. To rule out specific keys, you can
  use ?:not matchers or predicates.  For exact map matches, just use a literal
  map directly in the matcher."
  [[t & kv-pairs :as pattern] comp-env]
  (let [kv-pairs (cond-> kv-pairs
                   (odd? (count kv-pairs)) (concat ['?_]))
        comp-env (cond-> comp-env (= '?:map= t) (assoc :closed true))
        form (->> kv-pairs
               (partition 2)
               reverse
               (reduce (fn [m [k v]] (list '?:map-kv k v m)) nil))
        form (or form (if (:closed? comp-env)
                        '(?:literal {})
                        '(?:map-intersection {})))]
    (vary-meta (compile-pattern* form comp-env)
      assoc :pattern pattern)))

(defn- match-map-kv
  "
  ?:map-kv will match if the key is present and matches and the value is also present and matches.
  ?:maybe-key will match also if the key is not present, but if the key is present the value must match.
  ?:maybe-kv will match also if the key and value are present and match, but will still match if they can't match for any reason."
  [[t key-pattern value-pattern remainder :as pattern] comp-env]
  (let [key-matcher (compile-pattern* key-pattern comp-env)
        key-var (var-name key-pattern)
        literal-key (:literal (meta key-matcher))
        value-matcher (compile-pattern* value-pattern comp-env)
        literal-value (:literal (meta value-matcher))
        literal (when (and literal-key literal-value) (into literal-key literal-value))
        maybe-val? (= '?:maybe-kv t)
        maybe-key? ('#{?:maybe-key ?:maybe-kv} t)
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
                (let [on-value-match
                      (fn match2-succeed [new-dictionary n]
                        (let [remaining-map (dissoc the-map (key kv))]
                          (if remainder-matcher
                            (remainder-matcher [remaining-map] new-dictionary env)
                            (if (and closed? (seq remaining-map))
                              (on-failure :closed pattern new-dictionary env 1
                                remaining-map kv)
                              ((.succeed env) new-dictionary 1)))))]
                  (if-let [result
                           (value-matcher [(val kv)] dictionary
                             (assoc env :succeed on-value-match))]
                    result
                    (if maybe-val?
                      (on-value-match dictionary nil)
                      (on-failure :no-val-match pattern dictionary env 1
                        the-map (or (first literal-key) (:value (get dictionary key-var))))))))

              (scan-lookup-step [kv before after dictionary ^Env env matcher1 matcher2 retry key-has-matched?]
                (let [on-val-match
                      (fn match2-succeed [new-dictionary n]
                        (if remainder-matcher
                          (remainder-matcher [(into after before)] new-dictionary env)
                          (if (and closed? (or (seq before) (seq after)))
                            (on-failure :closed pattern new-dictionary env 1
                              (into after before) kv :retry retry)
                            ((.succeed env) new-dictionary 1))))]
                  (if kv
                    (let [after (dissoc after (key kv))]
                      ;; if val is literal match it first, otherwise always match on key first
                      (if-let [result (matcher1 kv dictionary
                                        (assoc env :succeed
                                          (fn match1-succeed [new-dictionary n]
                                            (vreset! key-has-matched? true)
                                            (matcher2 kv new-dictionary (assoc env :succeed on-val-match)))))]
                        result
                        (retry (conj before kv) after)))
                    (if (and maybe-key? (or maybe-val? (not @key-has-matched?)))
                      (on-val-match dictionary nil) ;; skip over matching this key and val and continue.
                      (on-failure :not-found pattern dictionary env 1 (into after before) nil :retry retry)))))

              (match-without-key [the-map dictionary env key-has-matched?]
                (scan-lookup-step nil nil the-map dictionary env nil nil nil key-has-matched?))]


        (let [[matcher1 matcher2] (if (and literal-value (not key-var))
                                    [->val ->key]
                                    [->key ->val])]
          (with-meta
            (cond literal-key
                  ;; fast path for the most common variant
                  (fn direct-lookup-matcher [data dictionary ^Env env]
                    (if (seq data)
                      (letfn [(map-key-matcher [the-map]
                                (if-let [kv (find the-map (first literal-key))]
                                  (on-direct-lookup kv the-map dictionary env)
                                  (if maybe-key?
                                    ;; This just takes the no match maybe-key? path within the scan-lookup-step:
                                    (match-without-key the-map dictionary env (volatile! false))
                                    (on-failure :not-found pattern dictionary env 1
                                      the-map (or (first literal-key) (:value (get dictionary key-var)))))))]
                        (let [the-map (first data)]
                          (if (and (map? the-map) (not (record? the-map)))
                            (if (seq the-map)
                              (map-key-matcher the-map)
                              (if maybe-key?
                                (match-without-key the-map dictionary env (volatile! false))
                                (on-failure :mismatch pattern dictionary env 1 data the-map)))
                            (on-failure :type pattern dictionary env 1 data the-map))))
                      (on-failure :missing pattern dictionary env 0 data nil)))

                  key-var
                  (fn bound-lookup-matcher [data dictionary ^Env env]
                    ;; if maybe-key?
                    (if (seq data)
                      (let [key-has-matched? (volatile! false)]
                        (letfn [(map-kv-item-lookup [the-map]
                                  (if-let [bound (get dictionary key-var)]
                                    (if-let [kv (find the-map (get bound :value))]
                                      (key-matcher [(key kv)] dictionary
                                        (assoc env :succeed
                                          (fn key-succeed [new-dictionary n]
                                            (vreset! key-has-matched? true)
                                            (on-direct-lookup kv the-map new-dictionary env))))
                                      (if maybe-key?
                                        (match-without-key the-map dictionary env key-has-matched?)
                                        (on-failure :not-found pattern dictionary env 1 the-map (:value bound) :retry retry)))
                                    (trampoline retry [] the-map)))
                                (map-kv-item-matcher [before after dictionary]
                                  (scan-lookup-step (first after) before after dictionary env matcher1 matcher2 retry key-has-matched?))
                                (retry [scanned-map remaining-map]
                                  (if (seq remaining-map)
                                    (bouncing (map-kv-item-matcher scanned-map remaining-map dictionary))
                                    (if maybe-key?
                                      (match-without-key scanned-map dictionary env key-has-matched?)
                                      (on-failure :mismatch pattern dictionary env 1 data remaining-map :retry retry))))]
                          (let [the-map (first data)]
                            (if (and (map? the-map) (not (record? the-map)))
                              (map-kv-item-lookup the-map)
                              (on-failure :type pattern dictionary env 1 data the-map :retry retry)))))
                      (on-failure :missing pattern dictionary env 0 data nil)))

                  :else
                  (fn map-search-matcher [data dictionary ^Env env]
                    (if (seq data)
                      (let [key-has-matched? (volatile! false)]
                        (letfn [(map-kv-item-matcher [before after dictionary]
                                  (let [kv (if literal-value
                                             ;; specialized fast scan for a matching literal
                                             (loop [before before after after kv (first after)]
                                               (when kv
                                                 (if (= (first literal-value) (val kv))
                                                   [before after kv]
                                                   (let [after (dissoc after (key kv))]
                                                     (recur (conj before kv) after (first after))))))
                                             [before after (first after)])
                                        [before after kv] (if (map-entry? kv) [before after kv] kv)]
                                    (scan-lookup-step kv before after dictionary env matcher1 matcher2 retry key-has-matched?)))
                                (retry [scanned-map remaining-map]
                                  (if (seq remaining-map)
                                    (bouncing (map-kv-item-matcher scanned-map remaining-map dictionary))
                                    (if maybe-key?
                                      (match-without-key scanned-map dictionary env key-has-matched?)
                                      (on-failure :mismatch pattern dictionary env 1 data remaining-map :retry retry))))]
                          (let [the-map (first data)]
                            (if (and (map? the-map) (not (record? the-map)))
                              (trampoline retry [] the-map)
                              (on-failure :type pattern dictionary env 1 data the-map :retry retry)))))
                      (on-failure :missing pattern dictionary env 0 data nil))))
            (merge (merge-meta (map meta [key-matcher value-matcher remainder-matcher]))
              {:length (len 1)
               `spliceable-pattern (fn [_] pattern)
               :expanded pattern})))))))

(defn- into-map [x]
  (apply array-map x))

(defn- even-length? [x]
  (even? (count x)))

(defn match-in-map [[t & kvs] comp-env]
  (let [kvs (cond-> kvs (odd? (count kvs)) (concat ['?_]))]
    (vary-meta
      (if (= '??:map= t)
        (vary-meta
          (compile-pattern*
            `(~'??:chain ~'??_ into-map (~'?:map ~@kvs))
            comp-env)
          update :length assoc :v false)
        (compile-pattern*
          `(~'??:chain (~'?? ~'_ (~'on-all even-length?)) into-map (~'?:map ~@kvs))
          comp-env))
      update :length assoc :n (count kvs))))

(defn match-+map
  "Create a ?:+map matcher than can match a key/value pair at least once."
  [[_ k v] comp-env]
  (compile-pattern* `(~'?:chain ~'?_ seq ((~'?:* ~[k v])))
    comp-env))

(defn match-*map
  "Create a ?:*map matcher than can match a key/value pair multiple times."
  [[_ k v] comp-env]
  (compile-pattern* `(~'?:chain
                      (~'? ~'_ ~(some-fn nil? map?))
                      seq (~'| nil ((~'?:* ~[k v]))))
                    comp-env))


(register-matcher '?:map-kv #'match-map-kv {:aliases '[?:maybe-key ?:maybe-kv]})
(register-matcher '?:map-intersection #'match-map-intersection)
(defgen= matcher-type [(every-pred map? (complement record?))] :map)
(register-matcher :map #'match-map-literal)
(register-matcher '?:map #'match-map {:aliases '[?:map=]})
(register-matcher '??:map #'match-in-map {:aliases '[??:map=]})
(register-matcher '?:+map #'match-+map {:aliases ['?:map+]})
(register-matcher '?:*map #'match-*map {:aliases ['?:map*]})
