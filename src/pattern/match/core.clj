(ns pattern.match.core
  (:refer-clojure :exclude [trampoline])
  (:require [genera :refer [defgenera defgenera= defgen defgen* defgen= defmethod* defmethod!
                            trampoline trampolining bouncing]]
            [uncomplicate.fluokitten.core :as f]
            [pattern.types :refer [->Length map->Env]]
            [pattern.match.predicator :refer [*pattern-replace*]]
            [pure-conditioning :as c :refer [condition restarts default manage restart-with handler-cond]]
            [clojure.string :as str]
            [clojure.walk :as walk])
  (:import pattern.types.Env))

;; match-utils

(defn len
  "Create a fixed-length Length object with the given min length."
  [n]
  (->Length n false))

(defn var-len
  "Create a variable-length Length object with the given min length."
  [n]
  (->Length n true))

(def ^:dynamic *disable-modes* false)

(defgenera var-name 1 [var]
  "Return the name for the variable if it has one."
  nil)
(defgenera matcher-type 1
  "Return the type indicator symbol for the variable if it is a matcher."
  [var] :value)

(defn var-key [name ^Env env]
  (when name
    (if-let [path ((.var_path env) name)]
      (conj path name)
      name)))

(defonce matcher-alias (atom {}))
(defonce matcher-type? (atom #{}))
(defonce named-matcher-type? (atom #{}))
(defonce restriction-position (atom {::default 2}))
(def ^:dynamic enable-restart-pattern? #{})

(defn matcher-type-for-dispatch
  "The same as matcher-type, but with aliases resolved."
  ([pattern]
   (matcher-type-for-dispatch pattern nil))
  ([pattern comp-env]
   (let [t (matcher-type pattern)]
     (@matcher-alias t t))))

(defmulti compile-pattern*
  "The multimethod patterns are registered to. This function is used within pattern combinators
  to instantiate child patterns."
  matcher-type-for-dispatch)

(defn register-matcher
  "Register a matcher combinator type with its compiler function.

  - matcher-type is a symbol used in a pattern to indicate the registered pattern type.

  - matcher-impl is a pattern compiler function that takes [pattern comp-env] and returns a
  (fn [data dictionary env]) with appropriate metadata indicating all var-names it or any of
  its child patterns contains together with their modes and prefixes, and the
  pattern length, which indicates minimum length and whether the pattern is
  variable length.

  Optionally, you may specify:

  - aliases: additional matcher-type symbols

  - named?: true if the pattern is named within the pattern and an appropriate
  implementation of var-name exists

  - restriction-position: the position in the list where a restriction function
  may optionally be included. ie 2 in the case of (? x restr?)"
  ([matcher-type matcher-impl]
   (register-matcher matcher-type matcher-impl {}))
  ([matcher-type matcher-impl {:keys [aliases named? restriction-position]}]
   (let [aliases (zipmap aliases (repeat matcher-type))]
     (swap! matcher-alias merge aliases)
     (swap! matcher-type? into (cons matcher-type (keys aliases)))
     (when named?
       (swap! named-matcher-type? conj matcher-type))
     (when restriction-position
       (swap! pattern.match.core/restriction-position assoc matcher-type restriction-position))
     (defmethod* compile-pattern* matcher-type matcher-impl))))

(defn listy?
  "Returns true if x is any kind of list except a vector."
  [x]
  (and (sequential? x) (not (vector? x))))

(defn named-matcher?
  "Returns truthy if the var is a list-style matcher type registered as named,
  and it has a name."
  [x]
  (and (listy? x)
       (@named-matcher-type? (matcher-type x))
       (or (symbol? (second x))
           (keyword? (second x)))))

(defn simple-named-var?
  "Returns a truthy value if x is a symbol starting with some number of ?'s
  followed by some other character, indicating a non-list variable."
  [x]
  (and (symbol? x)
       (= \? (first (name x)))
       (seq (drop-while #(= \? %) (name x)))))

(defn simple-ref?
  "Returns a truthy value if x is a symbol starting with $, indicating a ref insertion."
  [x]
  (and (symbol? x)
       (= \$ (first (name x)))
       (next (name x))))

(defn matcher-form-parts
  "If a matcher form is a symbol, return the result of matching it against a
  regex to extract the matcher-type parts and matcher-mode."
  [s]
  (when (symbol? s)
    (re-matches #"^([?]+)([^?:\w]*)(:\w+)?$" (name s))))

(defn matcher-form?
  "Returns the matcher-type symbol for a given form if it matches a registered
  matcher type."
  [x]
  (when (listy? x)
    (loop [s (first x)]
      (if (@matcher-type? s)
        s
        (when (symbol? s)
          (if (namespace s)
            (recur (symbol (name s)))
            (when-let [m (matcher-form-parts s)]
              (@matcher-type? (symbol (str (nth m 1) (nth m 3)))))))))))

(defn compiled-matcher?
  "Returns true if the matcher was compiled with (compile-pattern)"
  [m]
  (::matcher (meta m)))

(defn compiled*-matcher?
  "Returns true if the matcher was compiled with (compile-pattern*)"
  [m]
  (and (fn? m) (:var-names (meta m))))

(defgen* matcher-type [matcher-form?] matcher-form?)

(defgen matcher-type [simple-named-var?] [x]
  (symbol (apply str (take-while #{\?} (name x)))))
(defgen= matcher-type [sequential?] :list)
(defgen= matcher-type [simple-ref?] '?:ref)
(defgen= matcher-type [compiled-matcher?] :compiled-matcher)
(defgen= matcher-type [compiled*-matcher?] :compiled*-matcher)
(defgen= matcher-type [fn?] :plain-function)

(defgenera= matcher-mode 1
  "Return the mode portion of the matcher, which is a string of any
  non-alphanumeric characters (except :) immediately after the ? characters
  in the matcher symbol. Examples:

      ?x            -> nil
      ?<>x          -> \"<>\"
      ??<>x         -> \"<>\"
      (??>>> name)  -> \">>>\""
  nil)

(defgenera= matcher-prefix 1
  "Return the prefix portion of the matcher which is not included in the name.

  The prefix is the part of the name after the [[matcher-mode]] and before the
  first `:` character, or in a list-style matcher, it's the characters before the
  first `:` in the name.

  Examples:

    ?x                -> nil
    ?:x               -> nil
    ?t:x              -> \"t\"
    ?>>some-info:name -> \"some-info\"
    (? name)          -> nil
    (? info:name)     -> \"info\""
  nil)

(defgen matcher-mode [simple-named-var?] [x]
  (when-not *disable-modes*
    (let [s (->> (name x)
                 (re-matches #"^[?]+([^?:\w]*)[\w].*")
                 second)]
      (when-not (= "" s)
        s))))

(defgen matcher-mode [matcher-form?] [x]
  (when-not *disable-modes*
    (let [s (-> (first x)
                matcher-form-parts
                (nth 2))]
      (when-not (= "" s)
        s))))

(defgen matcher-prefix [simple-named-var?] [x]
  (let [s (->> (name x)
               (re-matches #"^[?]+[^?:\w]*(\w.*):[\w].*")
               second)]
    (when-not (= "" s)
      s)))

(def re-prefix-name #"(\w[^:]*):(\w.*)")

(defgen matcher-prefix [matcher-form?] [var]
  (let [n (name (nth var 1 ""))
        [_ prefix] (re-matches re-prefix-name n)]
    prefix))

(defn matcher-mode? [var mode]
  (when-let [m (matcher-mode var)]
    (str/includes? m mode)))

(defgen var-name [named-matcher?] [var]
  (let [s (nth var 1)
        sans-prefix (nth (re-matches re-prefix-name (name s)) 2 nil)]
    (if sans-prefix
      (symbol sans-prefix)
      (if (and (symbol? s) (not (namespace s)))
        s
        (symbol (name s))))))

(defgen var-name [simple-named-var?] [x]
  (if *disable-modes*
    (symbol (peek (re-matches #"^[?]+(.+)$" (name x))))
    (symbol ((some-fn second peek)
             (re-matches #"^[?]+[^?\w:]*(?:\w+:)?((?=[^:])\w.*)$|^[?]+(.+)$" (name x))))))

(defgen var-name [simple-ref?] [x]
  (symbol (apply str (rest (name x)))))

(defn resolve-fn
  "Attempts to return a function for the given form:

      symbol?   -> resolve the symbol in the global scope
      (apply x) -> recursively resolve x and return (partial apply x)
      ifn?      -> return the value literally. Works for function, keyword, map, set, etc.

  If the result is not resolved to `ifn?` then call `(fail)`"
  [form fail]
  (let [f (cond (symbol? form) (resolve form)
                (listy? form)
                (when (= 2 (count form))
                  (let [fm (first form)
                        fm (when (symbol? fm) (symbol (name fm)))]
                    (cond (#{'apply} fm)
                          (partial apply (resolve-fn (second form) fail))
                          (#{'on-each 'on-all} fm)
                          (resolve-fn (second form) fail))))
                form form)]
    (if (and form (not (ifn? f)))
      (fail)
      f)))

(defn var-restriction
  "Returns a function that takes a potential match value and returns true if the
  value is valid for the var"
  [var comp-env]
  (if (or (:ignore-predicates comp-env)
          (not (named-matcher? var)))
    [nil (constantly true)]
    (let [pos @restriction-position
          pos (pos (matcher-type var) (pos ::default))
          restr-part (drop pos var)
          form (first restr-part)
          arg-vars (next restr-part)
          form (when form
                 ;; either apply a transform provided in the comp-env or try to resolve the form directly
                 (or (some (fn [f] (f form))
                           ;; TODO: I think I should remove this. It's used in just one place
                           ;; to allow sequences to be restricted with just an integer representing count.
                           (:restrictions comp-env))
                     form))
          f-mode (when (and (listy? form) (symbol? (first form)))
                   ;; The possible valid modes could be configurable... They're just passed to the matcher
                   (#{'on-each 'on-all} (symbol (name (first form)))))
          f (resolve-fn form
                        #(throw (ex-info "Restriction did not resolve to a function" {:var var})))]
      [f-mode
       (if f
         (if arg-vars
           (let [arg-vars (map #(if (symbol? %) (var-name %) %)
                               arg-vars)]
             (fn apply-restriction [dictionary datum]
               (apply f datum (map (fn [v]
                                     (if (symbol? v)
                                       (get (get dictionary v) :value)
                                       v))
                                   arg-vars))))
           (fn restriction [dictionary datum] (f datum)))
         (constantly true))])))

(defn lookup [name dict env]
  (let [name (var-key name env)]
    (dict name)))

(defn sequence-lookup
  "Special version of lookup installed in the env when processing a sequence."
  [name dict env]
  (when-let [{val :value :as r} (lookup name dict env)]
    (let [val
          (if (seqable? val)
            (nth val (.repetition env) ::none)
            val)]
      (when (not= ::none val)
        (assoc r :value val)))))

(defn extend-dict [name value type abbr dict env]
  (let [name (var-key name env)]
    (if (or (nil? name) (= '_ name))
      dict
      (assoc dict name {:name name :value value :type type :abbr abbr}))))

(defn sequence-extend-dict
  "Special version of extend-dict installed in the env when processing a sequence."
  [name value type abbr dict env]
  (let [name (var-key name env)]
    (if (or (nil? name) (= '_ name))
      dict
      (letfn [(add-to-var [m]
                (if m
                  (-> m
                      (update :value
                              (fn [v]
                                (if (and (seqable? (:value m))
                                         (= (count (:value m))
                                            (.repetition env)))
                                  (conj v value)
                                  v)))
                      (assoc :abbr abbr))
                  {:name name :value [value] :type type :abbr abbr}))]
        (update dict name add-to-var)))))

(defn all-names [match-procedure]
  (with-meta
    (vec (:var-names (meta match-procedure)))
    (meta match-procedure)))

(defn all-values
  "A success continuation that returns a list of values in the order the vars
  are defined within the pattern."
  [match-procedure]
  (let [names (all-names match-procedure)]
    (fn [dict]
      (map (comp :value dict) names))))

(defn value-dict
  "A success continuation that creates a simple dictionary of :name -> value from
  the full match dictionary.

  Converts symbol names to keywords."
  [match-procedure]
  (let [names (all-names match-procedure)]
    (fn [dict]
      (reduce (fn [result name]
                (assoc result (keyword name) (get-in dict [name :value])))
              {} names))))

(defn symbol-dict
  "A success continuation that creates a simple dictionary of 'name -> value from
  the full match dictionary."
  [match-procedure]
  (let [names (all-names match-procedure)]
    (fn [dict]
      (reduce (fn [result name]
                (assoc result name (get-in dict [name :value])))
              {} names))))

(defn restartable? [pattern]
  (enable-restart-pattern? pattern))

(defn on-failure
  "This is called when a pattern fails, but typically just returns nil. If a
  variable is marked as restartable then this provides the signalling and
  continuation mechanisms via the pure-conditioning library."
  [type pattern dictionary env match-length data value & more-restarts]
  (when (restartable? pattern)
    (condition (keyword (name type) (name (or (var-name pattern) (matcher-type pattern))))
               (apply restarts (cond-> {:pattern pattern
                                        :dictionary dictionary
                                        :env env
                                        :match-length match-length
                                        :data data
                                        :value value
                                        :old-value (:value ((.lookup env) (var-name pattern) dictionary env))})
                      :force (fn force
                               ([] ((.succeed env) dictionary 1))
                               ([binding] (force binding 1))
                               ([binding match-length] ((.succeed env) ((.store env) (var-name pattern) binding '? dictionary env) match-length)))
                      :ignore (fn [] ((.succeed env) dictionary 0))
                      :fail false
                      more-restarts)
               (default false))))

;;;; matcher

(defn next-scope
  "This mechanism supports scoping within the match dictionary for ?:fresh variables."
  [f make-new-scope]
  (with-meta
    (fn the-next-scope [data dictionary ^Env env]
      (let [path-length (count (.scopes env))]
        (if (< path-length (dec (count @(.scope_path env))))
          (swap! (.scope_path env) update (dec path-length) inc)
          (swap! (.scope_path env) conj 0))
        (let [path (subvec @(.scope_path env) 0 path-length)
              new-scope (make-new-scope (last (.scopes env)) path)
              env (-> env
                      (update :scopes conj new-scope)
                      (assoc :var-path new-scope))]
          (f data dictionary env))))
    (meta f)))

(defmethod compile-pattern* :default [pattern comp-env]
  (throw (ex-info "Unknown matcher type" {:pattern pattern})))

(defn new-env
  [succeed]
  (map->Env {:succeed succeed
             :var-path {}
             :scopes [{}]
             :scope-path (atom [0])
             :lookup lookup
             :store extend-dict
             :repetition nil}))


(defn run-matcher
  "Run the given matcher on the given datum, calling succeed with the match
  dictionary if the matcher pattern.

  The dictionary is structured var-name -> {:name var-name
                                            :value matched-value
                                            :type matcher-type}"
  [match-procedure datum succeed]
  (match-procedure (list datum)
                   {}
                   (fn run-matcher-success [dict n]
                     (when (= n 1)
                       (succeed dict)))))

(defn compile-pattern
  "Compiles a pattern, returning a function that can be used in two different ways.

  Arity 1 is the user-friendly version. Use it to match against a piece of data, returning
  either nil or a result map of name -> value. For example, this pattern will match
  an unordered multiply expression:

      (let [find-unordered (compile-pattern '(* ?b (? a < ?b)))]
        (find-unordered '(* 1 2))  ;; => nil
        (find-unordered '(* 2 1))) ;; => {'b 2, 'a 1}

  Experimental: Patterns may be altered and recompiled via a special call to the
  arity-1 matcher:

      (let [p (compile-pattern '(+ 1 2 ?x))]
        (p ^::recompile (fn [orig-matcher compile pattern comp-env]
                          (compile (reverse pattern) comp-env)))
        (p '(9 2 1 +))) ;; => {x 9}

  The recompile function takes 4 arguments and must have ::recompile in its metadata. This is
  to support progressive construction of rules. It does not facilitate rule reuse because the
  recompiled rules are mutated in place with the new matcher."
  ([pattern]
   (compile-pattern pattern {}))
  ([pattern comp-env]
   (let [comp-env (assoc comp-env ::pattern-replace *pattern-replace*)
         compile (fn [pattern comp-env]
                   (compile-pattern* pattern
                                     (merge {:named-patterns (atom {})}
                                            comp-env)))
         f (atom (compile pattern comp-env))]
     (with-meta
       (fn matcher
         ([datum]
          (if (and (fn? datum) (::recompile (meta datum)))
            (swap! f datum compile pattern comp-env)
            (run-matcher matcher datum (value-dict @f))))
         ([data dictionary success]
          (@f data dictionary (new-env success))))
       (assoc (meta @f)
              :pattern pattern
              ::pattern-replace (::pattern-replace comp-env)
              ::matcher f)))))


(defn matcher
  "Compiles (and optionally executes) a matcher pattern.

  The result is either nil if no match is made or a list of matches for each
  variable in the pattern in the order they are defined.

  (let [find-unordered (matcher '(* ?b (? a < ?b)))]
    (find-unordered '(* 1 2))  ;; => nil
    (find-unordered '(* 2 1))) ;; => '(2 1)

  This style is useful for short or simple patterns but it becomes more
  challenging to maintain matcher ordering between the pattern and the result as
  the pattern complexity increases. To instead receive a dictionary of matches,
  use [[compile-pattern]] instead, which returns a function that, when called
  with just 1 argument returns either a dictionary of matches or nil.

  The compilation and execution process for this function and
  [[compile-pattern]] is identical."
  ([pattern]
   (let [match-procedure (compile-pattern pattern)]
     (with-meta
       (fn the-matcher [datum]
         (run-matcher match-procedure datum (all-values match-procedure)))
       (meta match-procedure))))
  ([pattern datum]
   ((matcher pattern) datum)))

(defn match?
  "Like [[matcher]] but simply returns true if matched successfully."
  ([pattern]
   (let [match-procedure (compile-pattern pattern)]
     (with-meta
       (fn the-matcher [datum]
         (run-matcher match-procedure datum (constantly true)))
       (meta match-procedure))))
  ([pattern datum]
   ((match? pattern) datum)))

(defn pattern-names
  "Return a list of all of the variable names defined in the pattern in the
  order the values will be returned when using [[matcher]].

      (let [find-unordered (matcher '(* ?b (? a < ?b)))]
          (pattern-names find-unordered)) ;; => (b a)

  This may be either passed a pattern directly or a pattern compiled either by
  [[compile-pattern]] or [[matcher]]"
  [pattern]
  (all-names (compile-pattern pattern {:ignore-predicates true})))
