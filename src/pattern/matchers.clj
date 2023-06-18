(ns pattern.matchers
  "This file contains the definitions of the nearly 20 built-in pattern matcher
  combinators.

  Matchers are registered with a handler function and a matcher-type symbol or
  keyword together with some meta information about the matcher such as whether
  it produces a named binding, has any aliases, etc.

  Each registered matcher is a function that compiles the raw pattern to a
  matcher combinator function. Each matcher combinator accepts data to be match,
  the current binding dictionary, and an environment that includes the success
  function which is called if the matcher successfully makes a match. If the
  matcher does not match it returns false.

  Some matchers can backtrack and try different combinations of input data. They
  do that by making an initial match and calling the success continuation with
  the match and associated bindings. If the match is not successful, the matcher
  can try a different combination of input data and call the success
  continuation again. This can happen as many times as necessary and results in
  effective backtracking behavior.

  Matcher combinators also have a set of metadata attached to them that
  describes the minimum match length, whether the match length is variable,
  captured variable names and any optional variable modes attached to the
  variable names. For recursive matchers such as list or sequence matchers, the
  metadata is a combination of the matcher's own metadata and that of its child
  matchers."
  (:refer-clojure :exclude [trampoline])
  (:use pattern.match.core)
  (:require [genera :refer [trampoline trampolining bouncing]]
            [uncomplicate.fluokitten.core :as f]
            [pattern.types :refer [spliceable-pattern]]
            [pattern.match.core :as m]
            [pattern.match.predicator :refer [var-abbr]])
  (:import (pattern.types Env)))

(set! *warn-on-reflection* true)

(defn- match-value
  "Match a value using [[clojure.core/=]] semantics."
  [pattern-const comp-env]
  (with-meta
    (fn const-matcher [data dictionary ^Env env]
      (if (seq data)
        (if (= (first data) pattern-const)
          ((.succeed env) dictionary 1)
          (on-failure :mismatch pattern-const dictionary env 1 data (first data)))
        (on-failure :missing pattern-const dictionary env 0 data (first data))))
    {:length (len 1)}))


(defn- match-literal
  "This is a way to match an escaped value, so for instance something
  that looks like a matcher can be matched this way."
  [[_ pattern] comp-env]
  (match-value pattern comp-env))


(defn- match-compiled
  "This simple matcher enables splicing in existing compiled matchers into a pattern.

  The only (?) exception is that splicing into a sequence matcher will not behave as
  expected because matchers within repeating patterns are configured with
  additional compile-time information not available to the pattern being spliced
  in."
  [m comp-env]
  @(::m/matcher (meta m)))


(defn- match-compiled*
  "This simple matcher enables the compiler to insert compiled matchers into a pattern."
  [m comp-env]
  m)

(defn- match-plain-function
  "If a plain function is inserted into a pattern, treat it as the function in
  an anonymous matcher with a restriction function."
  [f comp-env]
  (compile-pattern* (list '? '_ f) comp-env))

(defn add-lengths
  ([] nil)
  ([a b]
   (if (and a b)
     (let [na (:n a)
           va (:v a)
           nb (:n b)
           vb (:v b)]
       {:n (+ na nb) :v (or va vb)})
     (or a b))))

(defn and-lengths
  ([] nil)
  ([a b]
   (if (and a b)
     (let [na (:n a)
           va (:v a)
           nb (:n b)
           vb (:v b)]
       {:n (max na nb) :v (or va vb)})
     (or a b))))

(defn- build-child-matchers
  "Builds in reverse so that sequence matchers know how many elements to reserve
  after them, and their minimum required match size.

  Matchers are returned in the original order."
  [pattern comp-env]
  (first
    (reduce (fn [[matchers comp-env] p]
              (if-let [m (compile-pattern* p comp-env)]
                [(cons m matchers)
                 (update comp-env
                   :reserve-min-tail add-lengths (:length (meta m)))]
                [matchers comp-env]))
      [() (assoc comp-env :reserve-min-tail (len 0))]
      (reverse pattern))))

(defn- match-list
  "Match a list or vector. If the first symbol with in the list is ?:seq, allows
  the matcher to match any type of list. Otherwise if the pattern is a vector,
  must match a vector, or if a list, must be a type of list. The matcher doesn't
  make distinctions on the various list types, though.

  If the pattern is variable but the minimum length is longer than the list
  length, no matches will be attempted. Otherwise the pattern length must match
  before attempting to match its contents."
  [pattern comp-env]
  (let [[list-pred pattern] (let [token (first pattern)]
                              ;; If list starts with ?:seq symbol, match any seqable type.
                              (cond (and (symbol? token) (= "?:seq" (name token)))
                                    [seqable? (rest pattern)]
                                    (and (symbol? token) (= "?:list" (name token)))
                                    [list? (rest pattern)]
                                    :else
                                    [(if (vector? pattern) vector? seqable?) pattern]))
        matchers (build-child-matchers pattern comp-env)
        list-length (reduce add-lengths (map (comp :length meta) matchers))
        {match-length :n variable-length? :v} list-length
        match-length (or match-length 0)]
    (with-meta
      (fn list-matcher [data dictionary ^Env env]
        (if (seq data)
          (letfn [(list-item-matcher [datum data-list matchers dictionary]
                    (if (seq matchers)
                      (if-let [result
                               ((first matchers)
                                data-list
                                dictionary
                                ;; This construct would have to be carefully redesigned for trampoline
                                ;; (at least on sequence matches).
                                (assoc env :succeed
                                  (fn match-list-succeed [new-dictionary n]
                                    (if (> n (count data-list))
                                      (throw (ex-info "Matcher ate too much" {:n n}))
                                      (list-item-matcher datum (drop n data-list) (next matchers) new-dictionary)))))]
                        result
                        (on-failure :mismatch pattern dictionary env 1 data datum
                          :retry retry))
                      (if (empty? data-list)
                        ((.succeed env) dictionary 1)
                        (on-failure :too-long pattern dictionary env 1 data datum
                          :retry retry))))
                  (retry [data-list]
                    (if (list-pred data-list)
                      (bouncing (list-item-matcher data-list data-list matchers dictionary))
                      (on-failure :type pattern dictionary env 1 data data-list
                        :retry retry)))]
            (let [datum (first data)
                  c (when (sequential? datum) (count datum))]
              (when (if (and c variable-length?)
                      (<= match-length c)
                      (= match-length c))
                (trampoline retry datum))))
          (on-failure :missing pattern dictionary env 0 data nil)))
      {:var-names (distinct (mapcat (comp :var-names meta) matchers))
       :var-modes (apply merge-with f/op (map (comp :var-modes meta) matchers))
       :var-abbrs (apply merge-with f/op (map (comp :var-abbrs meta) matchers))
       :var-prefixes (apply merge-with f/op (map (comp :var-prefixes meta) matchers))
       :greedy (some (comp :greedy meta) matchers)
       :list-length list-length
       :length (len 1)
       `spliceable-pattern (fn [_] `(~'?:1 ~@pattern))})))

(defn- match-element
  "Match a single element.

  This matcher works in 2 forms: ?x or (? x). The short form is for convenience,
  while the list form enables matchers to have additional options specified.

  When using the list form, the matcher name is taken from the second position
  without transformation, but must be either a symbol or keyword. If using a
  keyword, it will be transformed to a symbol. Namespaces in matcher names are
  ignored.

  If the name is a single underscore, ?_ or (? _), the match will not be
  included in the result and will not be unified with other matchers with the
  same name.

  You can provide a predicate on the var in the third position.

     (? name pred?)
  "
  [variable comp-env]
  (let [[sat-mode sat?] (var-restriction variable comp-env)
        name (var-name variable)
        prefix (matcher-prefix variable)
        abbr (var-abbr prefix name)]
    (with-meta
      (fn element-matcher [data dictionary ^Env env]
        (if (seq data)
          (let [datum (first data)]
            (if (sat? dictionary datum)
              (if-let [{v :value} ((.lookup env) name dictionary env)]
                (if (= v datum)
                  ((.succeed env) dictionary 1)
                  (on-failure :mismatch variable dictionary env 1 data datum))
                ((.succeed env) ((.store env) name datum '? abbr dictionary env) 1))
              (on-failure :unsat variable dictionary env 1 data datum)))
          (on-failure :missing variable dictionary env 0 data nil)))
      (if (or (nil? name) (= '_ name))
        {:length (len 1)}
        {:var-names [name]
         :var-modes {name (matcher-mode variable)}
         :var-prefixes {name (if prefix [prefix] [])}
         :var-abbrs {name (if abbr [abbr] [])}
         :length (len 1)}))))

(defn- force-match
  "Experimental matcher for use within ?:chain to replace the matched value with
  the result of the chain expression. May be useful in other places, too. May
  just cause chaos.

  Example:

     ((rule '(?:chain ?x reverse (?:force x))) '(b a)) ;; => (a b)

  BUT WATCH OUT! Here, ?x is bound to (b a), matches the second instance inside
  ?:chain and gets reversed. Next, it matches (reverse x) with the final (a b) form.

  The tricky thing is that when the result is generated, ?x is used in all 3
  places, so the counterintuitive result is that ?x is reversed in all matched
  locations:

     ((rule '[?x (?:chain ?x reverse (?:force x)) ?x])
     '[(b a) (b a) (a b)])
     ;; => [(a b) (a b) (a b)]

  I don't know how this will behave in backtracking situations, but it may turn
  out to be an effective backtrack prevention mechanism..."
  [[_ name] comp-env]
  (with-meta
    (fn force-matcher [data dictionary ^Env env]
      (if (seq data)
        (let [datum (first data)
              abbr nil] ;; TODO: get existing abbr from existing match if it exists
          ((.succeed env) ((.store env) name datum '?:force abbr dictionary env) 1))
        (on-failure :missing name dictionary env 0 data nil)))
    {:var-names [name]
     :length (len 1)}))

(defn- segment-equal? [orig-data value ok pattern dictionary env]
  (if (seqable? value)
    (loop [data orig-data
           value value
           n 0]
      (if (seq value)
        (if (= (first data) (first value))
          (recur (rest data) (rest value) (inc n))
          (on-failure :mismatch pattern dictionary env (inc n) orig-data (take (inc n) orig-data)))
        (if (empty? data)
          (ok n))))
    (on-failure :not-seqable pattern dictionary env 0 orig-data [])))

(defn- match-segment
  "Match 0-n elements. Comes in 2 flavors: ??x and (?? x). The list version
  allows restrictions similar to [[match-element]].

  Use the ! mode to make the matcher greedy: ??!x is greedy. Normally segment
  matchers are lazy (unlike the ?:* sequence matchers which are always greedy).

  If multiple segments match the same variable, the segments must be the same length.

  By default restrictions apply to each element individually. If you would like
  them to apply on aggregate, use (?? x (on-all f)), or if you want the value to
  be applied to a function, you can use (?? x (apply f))."
  [variable {:keys [reserve-min-tail] :as comp-env}]
  (let [[sat-mode sat? f?] (var-restriction variable
                             (update comp-env :restrictions
                               (fnil conj []) (fn [i] (when (int? i)
                                                       (list 'on-all #(= i (count %)))))))
        sat? (if f?
               (if (= 'on-all sat-mode)
                 sat?
                 (fn [dict s] (every? #(sat? dict %) s)))
               sat?)
        force-greedy (not (:v reserve-min-tail)) ;; no later list matchers are variable-sized.
        reserved-tail (or (:n reserve-min-tail) 0)
        name (var-name variable)
        prefix (matcher-prefix variable)
        abbr (var-abbr prefix name)
        greedy? (matcher-mode? variable "!")
        [loop-start loop-continue? loop-next update-datum]
        (if (or force-greedy greedy?)
          [identity
           (if force-greedy
             = ;; don't shrink to impossible sizes
             (fn [i n] (<= 0 i)))
           dec
           (fn [datum data len]
             (if (empty? datum) datum (pop datum)))]
          [(constantly 0) <= inc
           (fn [datum data len]
             (if (> len (count datum))
               (conj datum (nth data (count datum)))
               datum))])]
    (with-meta
      (fn segment-matcher [data dictionary ^Env env]
        (if-let [binding ((.lookup env) name dictionary env)]
          (let [bound (:value binding)]
            (segment-equal?
              (if (sequential? bound)
                (take (count bound) data)
                bound)
              bound
              (fn segment-match [n] ((.succeed env) dictionary n))
              variable dictionary env))
          (let [n (- (count data) reserved-tail)]
            (loop [i (loop-start n) datum (vec (take i data))]
              (when (loop-continue? i n)
                (or (and (sat? dictionary datum)
                      ((.succeed env) ((.store env) name datum '?? abbr dictionary env) i))
                  (recur (loop-next i) (update-datum datum data n))))))))
      (->
        (if (or (nil? name) (= '_ name))
          {:length (var-len 0)}
          {:var-names [name]
           :var-modes {name (matcher-mode variable)}
           :var-prefixes {name (if prefix [prefix] [])}
           :var-abbrs {name (if abbr [abbr] [])}
           :greedy greedy?
           :length (var-len 0)})
        (assoc `spliceable-pattern (fn [this] variable))))))

(defn- match-as
  "This matcher allows you to capture the overarching pattern matched by some
  arbitrary matcher.

      (?:as name [?some ?pattern]) or (?:as name ??seq)

  DEPRECATED BEHAVIOR:
  May result in being either a sequence or a single element matcher, depending
  on the behavior of the child matcher.  If the capture length is 1, it assumes
  that it is not a sequence matcher in that case. When I fix this it'll likely
  be a breaking change.

  To capture a sequence, use ?:as*, which will not behave differently depending on
  the matched sequence length.

      (?:as* name (?:* some pattern))

  Note also that ?:as will terminate matching on an empty sequence even if it contains
  a sequence matcher. ?:as* will allow the search to continue into the empty sequence,
  allowing the above to correctly match an empty sequence.

  Strictly, (?:as x ?y) could be replaced by (& ?x ?y)...

  Allows a restriction to be added, similar to [[match-element]]."
  [[t name pattern :as as-pattern] comp-env]
  (let [multi? (= '?:as* t)
        ;; TODO: can I look at the compiled pattern to automate the ?:as / ?:as* annoyance?
        m (compile-pattern* pattern comp-env)
        [sat-mode sat?] (var-restriction as-pattern comp-env)
        name (if (namespace name) (symbol (clojure.core/name name)) name)]
    (with-meta
      (fn as-matcher [data dictionary ^Env env]
        (if (or multi? (seq data))
          (m data dictionary
            (assoc env :succeed
              (fn as-succeed [dict n]
                ;; FIXME: remove the length check and update all relevant
                ;; rules, etc to use either ?:as or ?:as*.
                (let [datum (if (or multi? (not= 1 n))
                              (vec (take n data))
                              (first data))]
                  (if (sat? dict datum)
                    (if-let [{v :value} ((.lookup env) name dict env)]
                      (if (= v datum)
                        ((.succeed env) dict n)
                        (on-failure :mismatch as-pattern dictionary env n data datum))
                      ((.succeed env) ((.store env) name datum '?:as nil dict env) n))
                    (on-failure :unsat as-pattern dictionary env n data datum))))))))
      (merge-with f/op
        {:var-names [name]
         :var-modes {name (matcher-mode as-pattern)}}
        (meta m)))))


(defn- match-map
  "Match map datastructures. For instance to match {:from 1 :to 10}:

      (?:map :from ?f :to ?t)

  Map keys can be matched as literal values or as a simple named matcher where the
  bound name will already be bound to the key value before this matcher is encountered.

  For bound key lookups, this matcher does not currently perform a search, and does
  nothing with the matcher beyond use its bound value! (All of this is TODO). Any
  pattern or predicate in the key position will be ignored.

  This could work:
     (?:map :addr ?addr ?addr ?info)
  But this will not unless ?addr is bound before this statement is matched:
     (?:map ?addr ?info :addr ?addr)

  These matchers do not fail if there are extra keys. To rule out specific keys,
  you can use ?:not matchers or predicates. For exact map matches, just use a
  literal map directly in the matcher. To do matching against keys, use ?:chain.

  This does not use {:a ?x :b ?y} syntax for the matcher because key order may
  not be stable and it is important for the rule engine which uses matcher keys
  to generate function signatures."
  [[_ & kv-pairs :as pattern] comp-env]
  (assert (even? (count kv-pairs))
          "Map matcher must have an even number of key-matcher pair arguments.")
  (let [keys (vec (take-nth 2 kv-pairs))
        key-var-names (into [] (map var-name) keys)
        vals (mapv #(compile-pattern* % comp-env)
                   (take-nth 2 (rest kv-pairs)))]
    (with-meta
      (fn map-matcher [data dictionary ^Env env]
        (let [m (first data)]
          (if (map? m)
            (let [inner-env (assoc env :succeed (fn [dict n] dict))]
              (loop [dict dictionary
                     [k :as keys] keys
                     [kvn :as key-var-names] key-var-names
                     [v :as vals] vals]
                (if (seq keys)
                  (if-let [kv (if kvn
                                ;; TODO: expand this to search the keyspace if
                                ;; the key is not already bound.
                                (if-let [binding ((.lookup env) kvn dict env)]
                                  (find m (:value binding))
                                  (throw (ex-info "Map pattern with unbound key binding"
                                           {:key k :key-var-name kvn :pattern pattern})))
                                (find m k))]
                    (if-let [dict (v (list (val kv)) dict inner-env)]
                      (recur dict (rest keys) (rest key-var-names) (rest vals))
                      (on-failure :value pattern dict env 1 data m))
                    (on-failure :key pattern dict env 1 data m))
                  ((.succeed env) dict 1))))
            (on-failure :not-map pattern dictionary env 1 data m))))
      (assoc (apply merge-with f/op (map meta vals))
             :length (len 1)))))

(defn into-map [x]
  (apply hash-map x))

(defn match-in-map [[_ & kvs] comp-env]
  (compile-pattern* `(~'??:chain ~'??_ into-map (~'?:map ~@kvs))
                    comp-env))

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

(defn match-*set
  "Create a ?:set matcher than can match the items in a set."
  [[_ item] comp-env]
  (compile-pattern* `(~'?:chain
                      (~'? ~'_ ~(some-fn nil? set?))
                      seq (~'| nil ((~'?:* ~item))))
    comp-env))

(defn- match-optional
  "Match the given form 0 or 1 times. There may be any number of separate
  matcher patterns within this form, which all must match sequentially to make a
  single successful match. If any of the contained matchers fail, all of them
  will fail.

  This matcher is used as the repeating element for [[match-sequence]]."
  [[_ & pattern :as full-pattern] comp-env]
  (when (seq pattern)
    (let [mode (:optional/mode comp-env)
          optional? (nil? mode) ;; used directly via ?:?
          one? (= :one mode)
          many? (= :sequence mode)
          comp-env (dissoc comp-env :optional/mode)
          md-matcher (compile-pattern* pattern comp-env)
          md (meta md-matcher)
          step-size (max 1 (:n (:list-length md)))
          var-len? (:v (:list-length md))
          greedy? (and var-len? (:greedy md))
          tail-var (gensym 'tail)
          ;; TODO: if reserve-min-tail is set, chop the tail off before hitting the list-matcher
          ;; TODO: if reserve-min-tail is set and the pattern is not var, don't include the pattern?
          tail-pattern (symbol (str "??" tail-var))
          list-matcher (compile-pattern* (concat pattern (list tail-pattern)) comp-env)]
      (with-meta
        (fn optional-matcher [data orig-dictionary ^Env env]
          (let [env (update env :tails conj tail-var)]
            (letfn [(optional-segment-matcher [dict n size this-data]
                      (bouncing
                        (or
                          (list-matcher [this-data] dict
                            (assoc env :succeed
                              (fn opt-succeed [dict' _] ;; size returned by list matcher is always 1.
                                (let [tail (get dict' tail-var)
                                      tail-size (count tail)
                                      size (- size tail-size)
                                      dict' (dissoc dict' tail-var)]
                                  (or ((.succeed env) dict' (+ n size))
                                    (when (and many? (seq tail))
                                      (optional-segment-matcher dict' (+ n size) tail-size tail)))))))
                          (when optional? ((.succeed env) dict 0)))))]

              (if (seq data)
                (trampolining (optional-segment-matcher orig-dictionary 0 (count data) data))
                (when optional? ((.succeed env) orig-dictionary 0))))))
        (cond-> (meta md-matcher)
          true (assoc :length (:list-length md)
                 :pattern full-pattern)
          (not one?) (assoc-in [:length :v] true)
          (not one?) (assoc-in [:length :n] 0))))))

(defn- match-one
  "Match the given set of patterns once."
  [[t & pattern] comp-env]
  (if (< 1 (count pattern))
    (match-optional (list* t pattern) (assoc comp-env :optional/mode :one))
    (when (seq pattern)
      (compile-pattern* (first pattern) comp-env))))


(defn- has-n?
  "Try to be fast at checking whether a list or vector has at least n elements."
  [n data]
  (or (zero? n)
    (not= ::no (nth data (dec n) ::no))))

(defn- match-sequence
  "Match the given pattern repeatedly. A minimum and maximum number of matches
  may be specified.

      (?:* ?a ?b) ;; min 0 pairs

      (?:+ ?a)    ;; min 1 match

      (?:+ 1 2 3) ;; min 1 group of 3

      (?:* ?x (?:* ?y ?z) ?w) ;; sequence matcher within sequence matcher.

  A nicer way to specify min/max may be to use (?:n [2 10] ?x ?y). The effect
  is the same

      (?:* ^{:min 2 :max 10} ?x ?y) ;; between 2 and 10 (inclusive) pairs.

  NOTE, to capture an entire sequence use ?:as*

      (?:as* x (?:* inner pattern))

  If you use ?:as instead, a match of a single repetition will return the first
  element of the collection instead of the collection of length 1, causing
  an annoying bug hunt.

  Like [[match-optional]] (which this builds upon), the repeating pattern may be
  a sequence of multiple matchers.

  This matcher is greedy, and first gathers up all matches that it can, up to
  the `at-most` value, collecting the intermediate matches along the way. Once
  it's gathered all matches, it attempts to succeed with the longest match set,
  working backwards until either no downstream matchers fail or it runs below
  the `at-least` minimum valid match count. If at-least is not specified, the
  minimum is 0, in which case the matcher will always succeed."
  [at-least at-most [_ p0 :as pattern] comp-env]
  (when (next pattern)
    (let [min-pattern-size (:min (meta p0) 0)
          at-least (cond (not at-least) min-pattern-size
                         (symbol? at-least) at-least
                         :else (max at-least min-pattern-size))
          at-most (if (symbol? at-most) at-most (or at-most (:max (meta p0)) Long/MAX_VALUE))
          match-part (match-optional pattern (assoc comp-env :optional/mode :sequence :reserve-min-tail nil))
          matcher-vars (:var-names (meta match-part))
          reserve-min-tail (or (:reserve-min-tail comp-env) (len 0))
          reserve-min-tail (let [l (:length (meta match-part))]
                             (if (pos? (:n l))
                               ;; need to fit whole repetitions
                               (add-lengths reserve-min-tail (len (mod (:n reserve-min-tail)
                                                                    (:n l))))
                               reserve-min-tail))]
      (letfn [(test-match [reps dict]
                (let [evars (:sequence/existing dict)]
                  (and (if (symbol? at-least)
                         ;; no match if undefined
                         (<= (max (:value (dict at-least) Long/MAX_VALUE) min-pattern-size) reps)
                         (<= at-least reps))
                    (every? #(if-let [existing (evars %)]
                               (when (contains? dict %)
                                 (let [evalue (:value existing)]
                                   (if (sequential? evalue)
                                     (= (take reps evalue)
                                       (let [val (:value (dict %))]
                                         (if (sequential? val)
                                           (take reps val)
                                           val)))
                                     (= evalue (:value (dict %))))))
                               true)
                      matcher-vars))))
              (level-sequences [reps dict]
                ;; Ensure that all sequences are the same length, even if some matchers are optional.
                (reduce (fn [dict var-name]
                          (let [entry (dict var-name)
                                val (:value entry)]
                            (if (and (sequential? val)
                                  (< (count val) reps))
                              (update-in dict [var-name :value] conj nil)
                              dict)))
                  dict matcher-vars))
              (gather [dict n data env matches]
                (if (and (if (symbol? at-most)
                           ;; no match if undefined
                           (< (.repetition ^Env env) (:value (dict at-most) 0))
                           (< (.repetition ^Env env) at-most))
                      (has-n? (:n reserve-min-tail) data))
                  (bouncing
                    (or (match-part
                          data dict
                          (assoc env
                            :succeed
                            (fn seq-succeed [dict n']
                              (let [reps (inc (.repetition ^Env env))
                                    dict (level-sequences reps dict)]
                                (gather dict (+ n n') (drop n' data)
                                  (assoc env :repetition reps)
                                  (if (test-match reps dict)
                                    (conj matches [dict (+ n n')])
                                    matches))))))
                      matches))
                  matches))]
        (with-meta
          (fn many-matcher [data dictionary ^Env env]
            (let [dict (reduce (fn [d var] ;; Populate the dictionary with a set of empty matches if none exist
                                 (update d var #(or % {:name var :value [] :type '?:*})))
                         (assoc dictionary
                           :sequence/existing (select-keys dictionary matcher-vars)
                           :sequence/id (gensym))
                         matcher-vars)
                  matches
                  (trampolining
                    (gather dict 0 data
                      ;; Alter lookup behavior and make no-match in match-optional fail
                      (assoc env
                        :lookup sequence-lookup
                        :store sequence-extend-dict
                        :repetition 0)
                      (if (test-match 0 dict)
                        [[dict 0]]
                        [])))]
              (loop [matches matches]
                (when-let [[dict n] (peek matches)]
                  (or ((.succeed env) dict n)
                    (recur (pop matches)))))))
          (-> (meta match-part)
            (update :length (fn [l]
                              (if (symbol? at-least)
                                (var-len (:n l))
                                (if (and at-least (= at-least at-most))
                                  (len (* (:n l) at-least))
                                  (var-len (* (:n l) (or at-least 0)))))))
            (assoc
              :greedy (not= at-least at-most) ;; only not greedy if fixed-length
              `spliceable-pattern (fn [_] `(~'?:n [~at-least ~at-most] ~@(rest pattern))))))))))

(defn- match-many
  "See [[match-sequence]]"
  [pattern comp-env]
  (match-sequence 0 nil pattern comp-env))

(defn- match-at-least-one
  "See [[match-sequence]]"
  [pattern comp-env]
  (match-sequence 1 nil pattern comp-env))

(defn- match-n-times
  "See [[match-sequence]]"
  [[t n & pattern] comp-env]
  (let [[low high] (if (vector? n)
                     n
                     [n nil])]
    (match-sequence low high (cons t pattern) comp-env)))

(defn- match-chain
  "This is the power tool matcher. It alternates, working left to right between
  matcher and arbitrary function call.  The matched value may have a function
  applied to it, which can then be matched against and also have a function
  called against it, etc in a chain.

      (?:chain ?data
               meta ?metadata
               keys ?_
               count ?num-keys)

  The above example matches ?data normally but then also calls `meta` on that
  value, then keys to get the map keys of the metadata, ignores that value in
  the matcher, but then calls count and matches against the resulting key count."
  [[chain-type pattern & fn-pattern-pairs] comp-env]
  (let [matchers (mapv #(compile-pattern* % comp-env)
                   (cons pattern (take-nth 2 (rest fn-pattern-pairs))))
        fns (mapv (fn [edge]
                    (or (resolve-fn edge
                          #(throw (ex-info "Chain link did not resolve to a function" {:edge edge})))
                      (constantly true)))
              (take-nth 2 fn-pattern-pairs))
        extract (if (= '??:chain chain-type)
                  identity
                  first)]
    (with-meta
      (fn chain-matcher [data dict ^Env env]
        (letfn [(do-fn [matchers [f :as fns] data dict taken]
                  (if f
                    (do-match matchers (rest fns) [(f (extract data))] dict taken)
                    (bouncing ((.succeed env) dict taken))))
                (do-match [[m :as matchers] fns data dict taken]
                  (if m
                    (m data dict
                      (assoc env :succeed
                        (fn chain-succeed [dict n]
                          (do-fn (rest matchers) fns (take n data) dict (or taken n)))))
                    (when taken
                      (bouncing ((.succeed env) dict taken)))))]
          (trampoline do-match matchers fns data dict nil)))
      (-> (assoc (apply merge-with f/op (map meta matchers))
            :length (:length (meta (first matchers))))
        (update :var-names distinct)))))

(defn- match-some
  "Examples:

    (?:some name pred-to-match?)

  Yeah... there are 2 places to possibly name the matching item, but the second one
  can be used for patterns while the first one simply names the match, so they
  are differently useful. The latter matcher part is optional.

    (??:some name pred-to-match?
       [[??non-matching-items-before] ?matching-item [??unchecked-items-after]])"
  [[match-type name pred-name result-pattern] comp-env]
  (let [pred (resolve-fn pred-name
               #(throw (ex-info "Some predicate did not resolve to a function" {:pred pred-name})))
        result-matcher (when result-pattern
                         (compile-pattern* result-pattern comp-env))
        vlen? (= '??:some match-type)]
    (with-meta
      (fn some-matcher [data dictionary ^Env env]
        (if (seq data)
          (let [[datum match-len] (if vlen? [data (count data)] [(first data) 1])]
            (if (sequential? datum)
              (let [binding ((.lookup env) name dictionary env)
                    bound-value (:value binding)]
                ;; - break the loop below into a fn that I can start with any before/after state.
                ;; - when a match,
                ;;   - if the var doesn't match, keep trying
                ;;   - create the next dict
                ;;   - if there is no result-matcher, just succeed
                ;;   - try the result-matcher.
                ;;     - If it succeeds then the matcher succeeds
                ;;       (because we add to the dict before recurring the match must be valid)
                ;;     - if the result-matcher fails, resume the loop again from where we left off.
                (loop [before [] after (vec datum)]
                  (if (seq after)
                    (let [cur (first after)]
                      (if (and (or (not binding) (= bound-value cur))
                            (pred cur))
                        (let [dict (if binding
                                     dictionary
                                     ((.store env) name cur match-type nil dictionary env))]
                          (if result-matcher
                            ;; no need to modify the success function
                            (if-let [result (result-matcher [[before cur (subvec after 1)]] dict
                                              (assoc env :succeed
                                                (fn some-succeed [dict n]
                                                  ((.succeed env) dict match-len))))]
                              result
                              (recur (conj before cur) (subvec after 1)))
                            ((.succeed env) dict match-len)))
                        (recur (conj before cur) (subvec after 1))))
                    (on-failure :not-found pred-name dictionary env 1 data datum))))
              (on-failure :not-sequential name dictionary env 1 data datum)))
          (on-failure :missing name dictionary env 0 data nil)))
      (assoc
        (merge-with f/op
          (meta result-matcher)
          {:var-names [name]})
        :length (if vlen? (var-len 1) (len 1))))))


(defn- match-filter
  "Examples:

    (?:filter pred-to-match [??matches])
    (?:remove pred-to-remove [??matches])

    (??:filter pred-to-match [??matches])
    (??:remove pred-to-remove [??matches])

  Matches the entire collection if at least one member matches the predicate."
  [[match-type pred-name result-pattern :as pattern] comp-env]
  (let [pred (resolve-fn pred-name
               #(throw (ex-info "Some predicate did not resolve to a function" {:pred pred-name})))
        pred (if ('#{?:remove ??:remove} match-type) (complement pred) pred)
        result-matcher (compile-pattern* result-pattern comp-env)
        vlen? ('#{??:filter ??:remove} match-type)]
    (with-meta
      (fn some-matcher [data dictionary ^Env env]
        (if (seq data)
          (let [[datum match-len] (if vlen? [data (count data)] [(first data) 1])]
            (if (sequential? datum)
              (let [binding ((.lookup env) name dictionary env)
                    bound-value (:value binding)
                    matching (into [] (filter pred) datum)]
                (if (seq matching)
                  (result-matcher [matching] dictionary
                    (assoc env :succeed
                      (fn filter-succeed [dict n]
                        ((.succeed env) dict match-len))))
                  (on-failure :not-found pred-name dictionary env match-len data datum)))
              (on-failure :not-sequential name dictionary env 1 data datum)))
          (on-failure :missing name dictionary env 0 data nil)))
      (cond-> (meta result-matcher)
        true (assoc :length (if vlen? (var-len 1) (len 1)))
        vlen? (assoc `spliceable-pattern (fn [this] pattern))))))

(defn- match-regex
  "Match a string with the given regular expression. To succeed, the regex must
  match against the string and the pattern must also match against the regex
  captures and unify correctly just like any other pattern. This matcher
  supports use in two ways.

  Full string matching requires that the regex consumes the entire string. The
  pattern provided as the second argument matches the vector of captures that is
  returned when calling [[re-matches]].

      (?:re-matches regex pattern)

  Partial or multiple matching via [[re-seq]] does not require the regex to
  consume the entire string. Instead of one vector of matches, this mode returns
  a vector of match vectors, each of which are structured the same as above.

      (?:re-seq regex pattern)

  Example of a naive email matcher:

      (?:re-matches #\"(.*)@(.*)\\.(com|org)\" [?full-email ?name ?domain ?tld])

  or you may just capture the entire result:

      (?:re-matches #\"(.*)@(.*)\\.(com|org)\" ?matches)"
  [[op regex capture-pattern] comp-env]
  (let [m (compile-pattern* capture-pattern comp-env)
        f (condp = op
            '?:re-matches re-matches
            '?:re-seq re-seq)]
    (with-meta
      (fn regex-matcher [data dictionary ^Env env]
        (if-let [str (first data)]
          (if-let [matches (when (string? str)
                             (f regex str))]
            (m (list (vec matches)) dictionary
              (assoc env :succeed
                (fn regex-succeed [dict n]
                  ((.succeed env) dict 1))))
            (on-failure :mismatch regex dictionary env 1 data str))
          (on-failure :missing regex dictionary env 0 data nil)))
      (merge (meta m)
        {:length (len 1)}))))


(defn- match-or
  "This matcher works much like a regular or statement. It will only match at most one of its
  patterns.

  A successful match must both match the input data an unify any of the element
  or sequence variables it contains if they appear multiple times in the
  pattern.

      [?a (?:or ?a ?b) ?b] ;; matches [1 1 3] or [1 3 3] but not [1 2 3]

  "
  [pattern comp-env]
  (let [matchers (mapv #(compile-pattern* % comp-env) (rest pattern))]
    (with-meta
      (fn or-matcher [data dictionary ^Env env]
        (if-let [result
                 (loop [matchers matchers]
                   (if (seq matchers)
                     (or ((first matchers) data dictionary env)
                         (recur (rest matchers)))))]
          result
          (on-failure :mismatch pattern dictionary env 1 data nil)))
      {:var-names (distinct (mapcat (comp :var-names meta) matchers))
       :var-modes    (apply merge-with f/op (map (comp :var-modes meta) matchers))
       :var-prefixes (apply merge-with f/op (map (comp :var-prefixes meta) matchers))
       :var-abbrs    (apply merge-with f/op (map (comp :var-abbrs meta) matchers))
       :length (let [lens (map (comp :length meta) matchers)]
                 (if (apply = lens)
                   (first lens)
                   (var-len (apply min (map :n lens)))))})))


(defn- match-and
  "In regular patterns, this will be useful for unifying variables.

      (& ?x ?y) ;; says that x and y have to be equal.

  It also allows applying multiple predicates.

      (& (? x this?) (? _ that?)) ;; binds x if both `(this? x)` and `(that? x)`

  This should also be useful for the graph matcher where multiple paths could
  originate from a single element."
  [pattern comp-env]
  (let [matchers (mapv #(compile-pattern* % comp-env) (rest pattern))]
    (with-meta
      (fn and-matcher [data dictionary ^Env env]
        (letfn [(and-expr-matcher [matchers dictionary n]
                  (if (seq matchers)
                    (if-let [r ((first matchers) data dictionary
                                (assoc env :succeed
                                  (fn and-succeed [dict n']
                                    (if (or (= n n') (nil? n))
                                      (and-expr-matcher (rest matchers) dict n')
                                      (on-failure :length-mismatch pattern
                                        dictionary env n' data nil)))))]
                      r
                      (on-failure :mismatch pattern dictionary env n data nil))
                    ((.succeed env) dictionary (or n 0))))]
          (and-expr-matcher matchers dictionary nil)))
      {:var-names (distinct (mapcat (comp :var-names meta) matchers))
       :var-modes    (apply merge-with f/op (map (comp :var-modes meta) matchers))
       :var-prefixes (apply merge-with f/op (map (comp :var-prefixes meta) matchers))
       :var-abbrs    (apply merge-with f/op (map (comp :var-abbrs meta) matchers))
       :length (let [lens (map (comp :length meta) matchers)]
                 (reduce and-lengths lens))})))


(defn- match-not
  "The not matcher is useful both for preventing unification two matched
  variables from being equal, and for ensuring that a match does not satisfy a
  given predicate.

      [?x (& (?:not x) (?:not _ even?) ?y)]

  Combining the not matcher with the and matcher as above is a useful pattern."
  [[_ pattern :as whole-pattern] comp-env]
  (let [matcher (compile-pattern* pattern comp-env)
        ;; Not sure about this... What is the match length of a not-matcher?
        match-len (:n (:length (meta matcher)))]
    (with-meta
      (fn not-matcher [data dict ^Env env]
        (let [result (volatile! true)]
          (matcher data dict (assoc env :succeed
                               (fn not-succeed [_ n]
                                 (vreset! result false)
                                 (on-failure :mismatch whole-pattern dict env n data nil
                                   :ignore (fn [] (vreset! result true))))))
          (if @result
            ((.succeed env) dict match-len))))

      (meta matcher))))


(defn- match-if
  "For chosing which match to perform purely based on a predicate, you can use
  this matcher or [[match-when]]. This matcher functions much like a regular if
  statement, but in the context of pattern matching is somewhat limited because
  it does not allow the predicate to match a sequence. However if it fits the
  purpose, it is a nice, simple and fast matcher.

      (?:if number? ?x ?y)

  For match-based or conditional matching, combine the & (and) and | (or)
  boolean logic matchers, which also allows sequence matching:

      (| (& pred-pattern conseq) alt)"
  [[_ pred conseq alt] comp-env]
  (let [pred (resolve-fn
              pred #(throw (ex-info "Predicate did not resolve to a function" {:pred pred})))
        conseq (compile-pattern* conseq comp-env)
        alt (when alt (compile-pattern* alt comp-env))]
    (with-meta
      (fn if-matcher [data dict ^Env env]
        (if (and (seq data) (pred (first data)))
          (conseq data dict env)
          (when alt (alt data dict env))))
      (if alt
        (assoc-in (merge-with f/op (meta conseq) (meta alt))
                  [:length :n] (min (:n (:length (meta conseq)))
                                    (:n (:length (meta alt)) 0)))
        (meta conseq)))))


(defn- match-when
  "This matcher works like [[match-if]] but since it does not have an else
  branch, it accepts multiple pattern statements to match if the predicate
  succeeds.

      [(?:when number? ?x ?y ?z)]

  Would match `[1 x y]` but not `[x y z]`.

  For match-based or conditional matching, use the & (and) matcher, which also
  allows sequence matching in the predicate:

      (& pred-pattern conseq)"

  [[t pred & conseq] comp-env]
  (match-if [t pred (match-one (list* t conseq) comp-env) nil] comp-env))


(defn- match-letrec
  "This construct purely defines named matchers that may be used within the
  pattern, and does not itself affect matching in any way.

  It is called letrec to make clear that the definition behavior is unordered,
  so within the letrec block, definitions can refer to each other regardless of
  the order that they are defined in.

  In this example, the pattern named B is referred to by A (using $B), then both
  A and B are used in the body pattern:

      (?:letrec [A [?a 2 $B]
                 B ?b]
        [$B $A ?a])

  Because this is a simple example it can be easily expanded out to an
  equivalent matcher. You can see that the named matchers defined within the
  letrec are considered to be in the same scope as the expression they are
  substituted into:

      [?b [?a 2 ?b] ?a]

  Paterns defined with `?:letrec` are inserted using `$pattern-name` via the
  [[match-ref]] matcher."
  [[_ bindings form] comp-env]
  (reset! (:named-patterns comp-env)
          (->> bindings
               (partition 2)
               (reduce (fn compile-bindings [np [name pattern]]
                         ;; NOTE: this uses mutability (kind of hacky). I want the pattern
                         ;; to resolve statically if possible and then fall back
                         ;; to dynamic resolution for circular refs. This enables
                         ;; that by aggressively adding data to the atom even while the
                         ;; data is being accumulated. In the end the total
                         ;; collection of named patterns is set at the top. Static resolution
                         ;; is done based on the information in :named-patterns at the time of compile.
                         ;;
                         ;; This just adds what we know so far for the benefit of the next compile:
                         (reset! (:named-patterns comp-env) np)
                         (assoc np name
                                (next-scope (compile-pattern* pattern comp-env)
                                            (fn [scope path] scope))))
                       @(:named-patterns comp-env))))
  (compile-pattern* form comp-env))


(defn- match-ref
  "This construct inserts named patterns created by [[match-letrec]] into the
  pattern via `$pattern-name`. The match length may be whatever the named
  pattern defines."
  [pattern comp-env]
  (let [name (var-name pattern)]
    (or (get @(:named-patterns comp-env) name)
        (with-meta
          (fn ref-matcher [data dictionary env]
            ((get @(:named-patterns comp-env) name)
             data dictionary env))
          {:length (var-len 0)}))))


(defn- match-fresh
  "Create a new scoped variable that is not related to any other variables of
  the same name. This is especially useful within named matchers or other
  matchers designed to be spliced into a pattern.

  Fresh variables may be used the same way as other variables, meaning that they
  can be used to unify multiple values in the pattern. An interesting example of
  this is the palindrome matcher, which recursively matches a palindromic
  pattern of arbitrary length.

      (?:letrec [palindrome
                 (| [(? x symbol?)
                     (?:fresh [x] $palindrome)
                     ?x]
                    [])]
        $palindrome)

  Which matches patterns like:

      '[a [b [c [] c] b] a]

  In this pattern, palindrome uses x at the parent scope, but before recurring
  creates a new scope for x, meaning that the next level is free to unify with
  anything again. The above would not match with `'[a [b [] XYZ] a]`, because
  the x at the first level of scoping can not unify b with XYZ.."
  [pattern comp-env]
  (let [[_ fresh form] pattern
        matcher (compile-pattern* form comp-env)]
    (assert (every? symbol? fresh))
    (assert (every? #(= :value (matcher-type %)) fresh))
    (vary-meta
     (next-scope matcher (fn [scope path]
                           (reduce (fn [scope name]
                                     (assoc scope name path))
                                   scope
                                   fresh)))
     update :var-names #(remove (set fresh) %))))


(defn- match-all-fresh
  "This allows composition of patterns which are not meant to unify with each
  other.

      (def other-pattern (compile-pattern '(?b ?c)))
      (def your-pattern (compile-pattern `(?a ?b (?:all-fresh ~other-pattern))))

  Without using all-fresh above, the above would only match if both instances of
  ?b unify, but with all-fresh, they would be treated separately inside and
  outside of the all-fresh form.

      (your-pattern '(1 2 (3 4))) ;;=> {:a 1 :b 2}

  The caveat is that the unifications within the ?:all-fresh block will not be
  included in the standard matcher results, but they can be accessed via

      (run-matcher your-pattern '(1 2 (3 4)) identity)

  which runs the matcher returning the raw internal results dictionary including
  matches that exist within nested scopes."
  [[_ pattern] comp-env]
  (let [matcher (compile-pattern* pattern comp-env)]
    (vary-meta
     (next-scope matcher (fn [scope path]
                           (reduce (fn [scope name]
                                     (assoc scope name path))
                                   scope
                                   (:var-names (meta matcher)))))
     assoc :var-names [])))


(defn- match-restartable
  "This construct does not define a matcher, but marks the pattern that it
  directly wraps as restartable, meaning that if it fails to match it will use
  the condition system to signal a restartable condition to enable it to recover
  from a failed match and resume. This is an experimental feature and not
  currently supported by all matchers.

      (?:restartable ?x)

  Makes the ?x pattern restartable. The restart could potentially force x to
  bind to an arbitrary value or force the match to continue even with x not
  bound to the value at that point.

  Even if a pattern is restartable, if a handler is not provided for a failure,
  the matcher will fail normally, meaning that conditions will not bubble up as
  exceptions unless the failure in question would normally raise an exception."
  [[_ pattern] comp-env]
  ;; TODO: Add a feature that allows matchers to advertise the restarts they make available. Right now because the
  (let [matcher (compile-pattern* pattern comp-env)]
    (with-meta
      (fn restartable-matcher [data dict env]
        (binding [enable-restart-pattern? (conj enable-restart-pattern? pattern)]
          (matcher data dict env)))
      (meta matcher))))


(register-matcher :value match-value)
(register-matcher :list #'match-list)
(register-matcher '?:= match-literal {:aliases ['?:literal]})
(register-matcher :compiled-matcher match-compiled)
(register-matcher :compiled*-matcher match-compiled*)
(register-matcher :plain-function #'match-plain-function)
(register-matcher '? #'match-element {:named? true})
(register-matcher '?? #'match-segment {:named? true})
(register-matcher '?:map #'match-map)
(register-matcher '??:map #'match-in-map)
(register-matcher '?:+map #'match-+map {:aliases ['?:map+]})
(register-matcher '?:*map #'match-*map {:aliases ['?:map*]})
(register-matcher '?:set #'match-*set)
(register-matcher '?:as #'match-as {:named? true :restriction-position 3})
(register-matcher '?:as* #'match-as {:named? true :restriction-position 3})
(register-matcher '?:? #'match-optional {:aliases ['?:optional]})
(register-matcher '?:1 #'match-one {:aliases ['?:one]})
(register-matcher '?:* #'match-many {:aliases ['?:many]})
(register-matcher '?:+ #'match-at-least-one {:aliases ['?:at-least-one]})
(register-matcher '?:n #'match-n-times {:aliases []})
(register-matcher '?:chain #'match-chain {:aliases ['??:chain]})
(register-matcher '?:force #'force-match)
(register-matcher '| #'match-or {:aliases ['?:or]})
(register-matcher '& #'match-and {:aliases ['?:and]})
(register-matcher '?:not #'match-not)
(register-matcher '?:if #'match-if)
(register-matcher '?:when #'match-when)
(register-matcher '?:letrec #'match-letrec)
(register-matcher '?:ref #'match-ref {:named? true})
(register-matcher '?:fresh #'match-fresh)
(register-matcher '?:all-fresh #'match-all-fresh)
(register-matcher '?:restartable match-restartable)
(register-matcher '?:re-matches #'match-regex)
(register-matcher '?:re-seq #'match-regex)
(register-matcher '?:some #'match-some {:named? true :aliases ['??:some]})
(register-matcher '?:filter #'match-filter {:aliases ['??:filter '?:remove '??:remove]})
