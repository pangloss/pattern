(ns pattern.matchers.set
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


(defn match-open
  "Maps and sets inside this block are matched 'open', meaning they may have extra elements not referenced by the matcher.

  This is the default behavior. It is present onl y to allow patterns inside a closed matcher to be reopened."
  [[_ pattern] comp-env]
  (compile-pattern* pattern (dissoc comp-env :closed?)))

(defn match-closed
  "Maps and sets inside this block are matched 'closed', meaning they may only have the elements referenced by the matcher.

  Setting this allows maps and sets that have no matchers inside them to be matched as literal values."
  [[_ pattern] comp-env]
  (compile-pattern* pattern (assoc comp-env :closed? true)))


(defn- match-set-intersection [[_ set-literal remainder :as pattern] comp-env]
  (vary-meta
    (compile-pattern*
      (list* '&
        '(? _ set?)
        (list '? '_ (fn check-intersection [x] (= set-literal (set/intersection set-literal x))))
        (when remainder
          [(list '?:chain '?_ (fn remove-known [x] (set/difference x set-literal))
             remainder)]))
      comp-env)
    assoc :expanded pattern))

(defn match-set-literal [the-set comp-env]
  (let [grouped (group-by #(:literal (meta (compile-pattern* % comp-env))) the-set)
        patterns (grouped nil)
        grouped-literals (dissoc grouped nil)
        closed? (:closed? comp-env)
        literals (when (seq grouped-literals)
                   (let [literal-set (set (apply concat (keys grouped-literals)))]
                     (if (and closed? (not (seq patterns)))
                       (list '?:= literal-set)
                       (list '?:set-intersection literal-set))))
        patterns (when (seq patterns)
                   (reduce (fn [m p] (list '?:set-item p m)) nil (reverse patterns)))]
    (compile-pattern*
      (if literals
        (if (seq patterns)
          (concat literals [patterns])
          literals)
        (if patterns
          patterns
          (if closed?
            (list '?:= #{})
            set?)))
      comp-env)))


(defn match-set [[t & items :as pattern] comp-env]
  (let [closed? ('#{?:set= ??:set=} t)
        flat? (re-find #"^\?\?:" (str t))
        comp-env (cond-> comp-env closed? (assoc :closed? true))]
    (vary-meta
      (if flat?
        (compile-pattern* (list '??:chain '??_ 'set (set items)) comp-env)
        (compile-pattern* (set items) comp-env))
      assoc :pattern pattern)))


(defn match-set-has
  "Create a ?:set-has matcher than can match an item in a set."
  [[_ item] comp-env]
  (compile-pattern* (list '?:chain '(? _ set?) seq (list '??_ item '??_)) comp-env))


(defn match-*set
  "Create a ?:*set matcher than matches all of the items in a set."
  [[_ item] comp-env]
  (compile-pattern* `(~'?:chain
                      (~'? ~'_ ~(some-fn nil? set?))
                      seq (~'| nil ((~'?:* ~item))))
    comp-env))

(defn- match-set-item
  "Match a list or vector. If the first symbol with in the list is ?:seq, allows
  the matcher to match any type of list. Otherwise if the pattern is a vector,
  must match a vector, or if a list, must be a type of list. The matcher doesn't
  make distinctions on the various list types, though.

  If the pattern is variable but the minimum length is longer than the list
  length, no matches will be attempted. Otherwise the pattern length must match
  before attempting to match its contents."
  [[t item remainder :as pattern] comp-env]
  (let [item-matcher (compile-pattern* item comp-env)
        literal (:literal (meta item-matcher))
        maybe? ('#{?:maybe-set-item ?:maybe-item ??:maybe-item} t)
        t ('{?:maybe-item ?:item ??:maybe-item ??:item ?:maybe-set-item ?:set-item} t)
        no-check-set? (or (#{'?:item '??:item} t) (= false (:check-set? comp-env)))
        closed? (:closed? comp-env)
        item-var (var-name item)
        remainder-matcher (when remainder (compile-pattern* remainder comp-env))
        remove-item (if no-check-set?
                      (fn [coll item]
                        (if (= item (first coll))
                          (rest coll)
                          (concat (take-while #(not= item %) coll) (next (drop-while #(not= item %) coll)))))
                      disj)
        find-item (if no-check-set?
                    (fn [coll item not-found]
                      (some #(when (or (= % item) (= % not-found)) %)
                        (concat coll [not-found])))
                    get)
        flat? (= '??:item t)
        extract (if flat? identity first)
        recombine (if no-check-set?
                    (fn [data after before]
                      (if (vector? (extract data))
                        (into [] (concat before after))
                        (concat before after)))
                    (fn [orig after before] (into after before)))]
    ;; TODO get the remainder length and add 1. We can check the set size
    ;; only check size before the first item
    (if (and literal closed? (not remainder))
      (compile-pattern* (list* '?:literal literal) comp-env)
      (with-meta
        (fn set-matcher [data dictionary ^Env env]
          (if (seq data)
            (letfn [(set-item-matcher [before after dictionary]
                      (let [found (if-let [bound (when item-var (get dictionary item-var))]
                                    (find-item after (:value bound) ::not-found)
                                    (first after))]
                        (if (and (= ::not-found found) (not maybe?))
                          (on-failure :not-found pattern dictionary env 1 (extract data)
                            (:value (get dictionary item-var)) :retry retry)
                          (let [datum (if (= ::not-found found) nil found)
                                after (remove-item after found)
                                succeed (fn match-set-succeed [new-dictionary n]
                                          (if remainder-matcher
                                            (let [remaining-set (recombine data after before)]
                                              (remainder-matcher [remaining-set] new-dictionary
                                                (if flat?
                                                  (assoc env :succeed
                                                    (fn flat-succeed [new-dictionary n]
                                                      ((.succeed env) new-dictionary
                                                       (count (extract data)))))
                                                  env)))
                                            (if (and closed? (or (seq before) (seq after)))
                                              (on-failure :closed pattern new-dictionary env 1
                                                (extract data) datum :retry retry)
                                              ((.succeed env) new-dictionary
                                               (if flat? (count (extract data)) 1)))))]
                            (if (= ::not-found found)
                              (succeed dictionary 0)
                              (if-let [result (item-matcher [datum] dictionary (assoc env :succeed succeed))]
                                result
                                (retry (if (= ::not-found found) before (conj before found)) after)))))))
                    (retry [scanned-set remaining-set]
                      (cond (seq remaining-set)
                            (bouncing (set-item-matcher scanned-set remaining-set dictionary))
                            maybe?
                            (bouncing (set-item-matcher scanned-set [::not-found] dictionary))
                            :else
                            (on-failure :mismatch pattern dictionary env 1 data remaining-set :retry retry)))]
              (let [the-set (extract data)]
                (if (or (set? the-set) no-check-set?)
                  (trampoline retry [] the-set)
                  (on-failure :type pattern dictionary env 1 data the-set :retry retry))))
            (on-failure :missing pattern dictionary env 0 data nil)))
        (merge (merge-meta (map meta [item-matcher remainder-matcher]))
          {;;:list-length list-length
           :length (cond flat? (var-len 1)
                         maybe? (var-len 0)
                         :else (len 1))
           `spliceable-pattern (fn [_] `(~'?:1 ~@pattern))})))))

(register-matcher '?:open #'match-open)
(register-matcher '?:closed #'match-closed)
(defgen= matcher-type [set?] :set) ;; register set literal
(register-matcher ':set #'match-set-literal) ;; register handler for set literal
(register-matcher '?:set #'match-set {:aliases '[??:set ?:set= ??:set=]})
(register-matcher '?:set-has #'match-set-has)
(register-matcher '?:set-item #'match-set-item {:aliases '[?:item ??:item ?:maybe-item ??:maybe-item]})
(register-matcher '?:set-intersection #'match-set-intersection)
(register-matcher '?:*set #'match-*set {:aliases ['?:set*]})
