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
        set?
        (fn check-intersection [x] (set/intersection set-literal x))
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

(defn match-set-has
  "Create a ?:set-has matcher than can match an item in a set."
  [[_ item] comp-env]
  (compile-pattern* (list '?:chain set? seq (list '??_ item '??_)) comp-env))


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
  [[_ item remainder :as pattern] comp-env]
  (let [item-matcher (compile-pattern* item comp-env)
        literal (:literal (meta item-matcher))
        closed? (:closed? comp-env)
        item-var (var-name item)
        remainder-matcher (when remainder (compile-pattern* remainder comp-env))]
        ;; TODO get the remainder length and add 1. We can check the set size
        ;; only check size before the first item
    (if (and literal closed? (not remainder))
      (compile-pattern* (list* '?:literal literal) comp-env)
      (with-meta
        (fn set-matcher [data dictionary ^Env env]
          (if (seq data)
            (letfn [(set-item-matcher [before after dictionary]
                      (let [datum (if-let [bound (when item-var (get dictionary item-var))]
                                    (let [bound-val (get after (:value bound) ::not-found)]
                                      (if (= ::not-found bound-val)
                                        (first after)
                                        bound-val))
                                    (first after))
                            after (disj after datum)]
                        (if-let [result
                                 (item-matcher
                                   [datum]
                                   dictionary
                                   (assoc env :succeed
                                     (fn match-set-succeed [new-dictionary n]
                                       (if remainder-matcher
                                         (let [remaining-set (into after before)]
                                           (remainder-matcher [remaining-set] new-dictionary env))
                                         (if (and closed? (or (seq before) (seq after)))
                                           (on-failure :closed pattern new-dictionary env 1
                                             (into after before) datum :retry retry)
                                           ((.succeed env) new-dictionary 1))))))]
                          result
                          (retry (conj before datum) after))))
                    (retry [scanned-set remaining-set]
                      (if (seq remaining-set)
                        (bouncing (set-item-matcher scanned-set remaining-set dictionary))
                        (on-failure :mismatch pattern dictionary env 1 data remaining-set :retry retry)))]
              (let [the-set (first data)]
                (if (set? the-set)
                  (trampoline retry [] the-set)
                  (on-failure :type pattern dictionary env 1 data the-set :retry retry))))
            (on-failure :missing pattern dictionary env 0 data nil)))
        (merge (merge-meta (map meta [item-matcher remainder-matcher]))
          { ;;:list-length list-length
           :length (len 1)
           `spliceable-pattern (fn [_] `(~'?:1 ~@pattern))})))))

(register-matcher '?:open #'match-open)
(register-matcher '?:closed #'match-closed)
(defgen= matcher-type [set?] :set) ;; register set literal
(register-matcher ':set #'match-set-literal) ;; register handler for set literal
(register-matcher '?:set-has #'match-set-has)
(register-matcher '?:set-item #'match-set-item)
(register-matcher '?:set-intersection #'match-set-intersection)
(register-matcher '?:*set #'match-*set {:aliases ['?:set*]})
