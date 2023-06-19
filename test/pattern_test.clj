(ns pattern-test
  (:require [clojure.test :refer :all]
            pattern.r3.core
            [pattern.match.core :as m :refer [matcher pattern-names var-name *disable-modes*
                                              compile-pattern matcher-prefix run-matcher]]
            [pattern.types :refer [not-meta?]]
            pattern.matchers
            [pure-conditioning :as c :refer [manage restart-with handler-cond]])
  (:use pattern.r3.core))

(deftest extensibility
  (let [<- (juxt m/matcher-type m/matcher-type-for-dispatch m/matcher-mode m/var-name)]
    (are [x y] (= x y)
      '[? ? nil a]             (<- '?a)
      '[? ? nil a]             (<- `?a)
      '[?? ?? ".$" b]          (<- '??.$b)
      '[?? ?? nil $$]          (<- '??$$)
      ;; an identifier-type can be hidden in a name before the first :
      '[?? ?? "->$" name]      (<- '??->$test:name)
      '[?? ?? "->$" x:name]    (<- '??->$test:x:name)
      '[?? ?? "->$" name]      (<- `??->$test:name)
      '[?? ?? "->$" x:name]    (<- `??->$test:x:name)
      ;; a : is not allowed in mode or as first char of name
      '[? ? nil ->$:test:name] (<- '?->$:test:name)
      '[? ? nil *:test:name]   (<- '?*:test:name)
      '[? ? nil ->$:test:name] (<- `?->$:test:name)
      '[? ? nil *:test:name]   (<- `?*:test:name)
      '[:list :list nil nil]   (<- '(+ ?a ?b))
      '[:value :value nil nil] (<- 1)
      '[:value :value nil nil] (<- '?)
      '[? ? nil b]             (<- '(? b))
      '[? ? "." b]             (<- '(?. b))
      '[?? ?? ".$" b]          (<- '(??.$ b))
      '[?:ref ?:ref "-" b]     (<- '(?-:ref b))
      '[:list :list nil nil]   (<- '(??:ref b))
      '[?:and & "." nil]       (<- '(?.:and b)))))

(deftest sequence-matching

  (is (nil? (matcher '[?x ??x] [1 1])))

  (is (= [[1]]
         (matcher '[?x ??x] [[1] 1])))

  (testing "list matcher mistakenly used seqable? instead of sequential? causing strings to be matched as lists."
    (is (nil? (matcher '((?:* ?x)) '"abc")))
    (is (nil? (matcher '(??x) '"abc"))))

  (is (= '(1 3)
         (matcher '[(?:? ?a ?b ?a +) ?b] '[1 3 1 + 3])))

  (is (= '(nil 3)
         (matcher '[(?:? ?a ?b ?a +) ?b] '[3])))

  (is (= '(1 3)
         (matcher '[(?:1 ?a ?b ?a +) ?b] '[1 3 1 + 3])))

  (is (nil?
       (matcher '[(?:1 ?a ?b ?a +) ?b] '[1 3 1 + 1 3 1 + 3]))
      "Don't match the optional pattern doubled")

  (is (nil?
       (matcher '[(?:1 ?a ?b ?a +) ?b] '[3])))

  (is (= [[1 1] [3 3]]
         (matcher '[(?:+ ?a ?b ?a +) ?b] '[1 3 1 + 1 3 1 + [3 3]]))
      "Sequence can match the optional pattern doubled (with slight change for the last ?b)")

  (is (= '(1 $$ (3))
         (matcher '[(?:? ?a ?x ?a +) ??b] '[1 $$ 1 + 3])))

  (is (= [1 '+ [2 '+]]
         (matcher '[(?:? ?x ?b) ??a] '[1 + 2 +])))

  (is (= [[1 2] '[+ +]]
         (matcher '[(?:* ?x ?y)] '[1 + 2 +])))

  (is (= [[1 2] '[+ +]]
         (matcher '[(?:* ^{:min 1 :max 5} ?x ?y)] '[1 + 2 +])))

  (testing "(?:n [min max] pattern)"
    (is (= [[1 2] '[+ +]]
          (matcher '[(?:n [1 5] ?x ?y)] '[1 + 2 +]))))

  (testing "(?:n min pattern)"
    (is (= [[1 2] '[+ +]]
          (matcher '[(?:n 1 ?x ?y)] '[1 + 2 +])))

    (is (= [[1 2] '[+ +]]
          (matcher '[(?:n 2 ?x ?y)] '[1 + 2 +])))

    (is (nil?
          (matcher '[(?:n 3 ?x ?y)] '[1 + 2 +]))))

  (testing "(?:n min-var pattern)"
    (is (= [1 [1 2] '[+ +]]
          (matcher '[?minvar [(?:n minvar ?x ?y)]] '[1 [1 + 2 +]])))

    (is (= [2 [1 2] '[+ +]]
          (matcher '[?minvar [(?:n minvar ?x ?y)]] '[2 [1 + 2 +]])))

    (is (nil?
          (matcher '[?minvar [(?:n minvar ?x ?y)]] '[3 [1 + 2 +]]))))

  (testing "(?:n [nil max-var] pattern)"
    (is (nil?
          (matcher '[?maxvar [(?:n [nil maxvar] ?x ?y)]] '[1 [1 + 2 +]])))

    (is (= [2 [1 2] '[+ +]]
          (matcher '[?maxvar [(?:n [nil maxvar] ?x ?y)]] '[2 [1 + 2 +]])))

    (is (= [3 [1 2] '[+ +]]
          (matcher '[?maxvar [(?:n [nil maxvar] ?x ?y)]] '[3 [1 + 2 +]]))))

  (testing "(?:n [min-var max-var] pattern)"
    (is (nil?
          (matcher '[?maxvar [(?:n [maxvar maxvar] ?x ?y)]] '[1 [1 + 2 +]])))

    (is (= [2 [1 2] '[+ +]]
          (matcher '[?maxvar [(?:n [maxvar maxvar] ?x ?y)]] '[2 [1 + 2 +]])))

    (is (nil?
          (matcher '[?maxvar [(?:n [maxvar maxvar] ?x ?y)]] '[3 [1 + 2 +]]))))

  (is (= [[1] ['+] [2 '+]]
         (matcher '[(?:* ^{:min 1 :max 5} ?x ?y) (?? z) ?x] '[1 + 2 + [1]])))

  (is (= [[1 2]]
         (matcher '[??x (?:* ?x)] [1 2 1 2])))
  (is (= [[1 2]]
         (matcher '[(?:* ?x) ??x] [1 2 1 2])))
  (is (= [[1] [1] 2 [1]]
         (matcher '[(?:* (& ?x ?a)) ?z (?:* (& ?x ?b)) ?z] [1 2 1 2])))
  (is (= [[1 2]]
         (matcher '[(?:+ ?x) (?:+ ?x)] [1 2 1 2])))
  (is (= [[1 2 1 2] []]
         (matcher '[(?:+ ^{:min 3} ?y) ??x] [1 2 1 2])))
  (is (= [[1 2 1 2] []]
         (matcher '[??!y (?:* ?x)] [1 2 1 2])))
  (is (= [[1 2 1 2] []]
         (matcher '[(?:+ ^{:min 3} ?y) (?:* ?x)] [1 2 1 2])))
  (is (= [[1] [2 1 2]]
         (matcher '[??!x (?:+ ^{:min 3} ?y)] [1 2 1 2])))
  (is (= [[1] [2 1 2]]
         (matcher '[??x (?:* ^{:max 3} ?y)] [1 2 1 2])))
  (is (= [[1 2]]
         (matcher '[??x ??x] [1 2 1 2]))))


(deftest negative-match
  (is (nil? (matcher '[?a (?:not ?a) 3] [1 1 3])))
  (is (= [1]
         (matcher '[?a (?:not ?a) 3] [1 2 3])))

  ;; this looks like a useful pattern:
  (is (nil? (matcher '[?a (& ?b (?:not ?a)) 3] [1 1 3])))
  (is (= [1 2]
         (matcher '[?a (& ?b (?:not ?a)) 3] [1 2 3]))))

(deftest ??:chain-test
  (testing "The ?? variant works with ?? matches against a captured sequence of data."
    (is (= [[2 1] [3]]
           (matcher '[(??:chain ??a (apply +) 3) ??b] [2 1 3])))
    (is (nil? (matcher '[(??:chain ??a (apply +) 4) ??b] [2 1 3])))
    (is (= [[2 1 3] []]
           (matcher '[(??:chain ??a (apply +) 6) ??b] [2 1 3])))
    (is (= [[] [2 1 3]]
           (matcher '[(??:chain ??a sort ?a) ??b] [2 1 3])))
    (is (= [[2] [1 3]]
           (matcher '[(??:chain ??!a sort ?a) ??b] [2 1 3])))
    (is (= [[2 1] [3]]
           (matcher '[(??:chain ??a sort (?:not ?a)) ??b] [2 1 3])))
    (is (= [[2 1 3] []]
           (matcher '[(??:chain ??!a sort (?:not ?a)) ??b] [2 1 3]))))
  (testing "The ?? variant can work with regular matches using apply"
    (is (nil?
         (matcher '(??:chain ?a (apply sort) ?a) [2 1 3])))
    (is (= [[2 1 3]]
           (matcher '(??:chain ?a (apply sort) (?:not ?a)) [2 1 3])))))

(deftest ?:chain-test
  (testing "The ? variant only works with ? matches against a single element."
    (is (nil?
         (matcher '(?:chain ?a sort ?a) [2 1 3])))
    (is (= [[2 1 3]]
           (matcher '(?:chain ?a sort (?:not ?a)) [2 1 3])))))

(deftest matching-maps-using-chain
  (testing "match a specific key"
    (is (= [1]
           (matcher '(??:chain ?_ (apply :a) ?ka)
                    {:a 1 :b 2})))

    (is (= [1]
           (matcher '(?:chain ?_ :a ?ka)
                    {:a 1 :b 2}))))

  (testing "matching unknown keys"
    (is (= [{:a 1, :b 1} :a 1 :b]
           (matcher '(?:chain ?a seq ([?k1 ?samev]
                                      [?k2 ?samev]))
                    {:a 1 :b 1})))

    (is (= [{:a 1, :b 1} [:a :b] [1 1]]
           (matcher '(?:chain ?a seq ((?:* [?keys ?vals])))
                    {:a 1 :b 1})))

    (is (= [{:a 1, :b 1} [:a :b] [1 1]]
           (matcher '(??:chain ?a (apply seq) ((?:* [?keys ?vals])))
                    {:a 1 :b 1})))))



(comment
  ;; This feature suffers from a complete lack of discoverability. Need to fix or remove.
  ;;
  (manage [:missing/x (restart-with (fn [c v d] (prn :missing c v) [:force 'x]))
           :mismatch/x (restart-with (fn [c v d] (prn :mismatch c v) [:force (:old-value v)]))
           :unsat/x (restart-with (fn [c v d] (prn :unsat c v) [:force (str (:old-value v))]))]
          (matcher '[?x (?:restartable ?x) (?:restartable (? x string?))] [1 2 99]))

  (var-name '?.x)
  (matcher-type '?.x)

  (manage :mismatch/list
          (matcher '(?:restartable [?x (? x string?) ?x]) [2 "2" 2]))

  (def trace
    (c/custom
     (fn [h d c n]
       (fn [v]
         (prn c v)
         nil))))

  (manage [:mismatch/list trace
           :too-short/list trace
           :too-long/list trace
           :missing/list trace
           :type/list trace]
          (matcher '(?:restartable [?x 1]) [1 1 1]))

  (binding [m/enable-restart-pattern? #{'[?x ?x 1]}]
    (manage [:mismatch/list trace
             :too-short/list trace
             :too-long/list trace
             :missing/list trace
             :type/list trace]
            (matcher '[?x ?x 1] [1])))

  ;; unmatchable pattern
  (binding [m/enable-restart-pattern? #{'[?x (? x string?) ?x]}]
    (manage [:mismatch/list c/trace]
            (matcher '[?x (? x string?) ?x] [2 "2" 2])))

  ,)

(deftest fresh-variable
  (is (= [1]
         (matcher '[?x (?:fresh [x]
                                [?x ?x]) ?x]
                  [1 [2 2] 1]))))

(deftest palindrome
  ;; This is much better than the original palindrome example! :D
  ;; It captures the data at the center that's not palindromic if it exists and
  ;; it also binds the first x and everything inside is fresh.
  (is (= '(a [d [] e])
         (matcher '(?:letrec [palindrome
                              (| [(? x symbol?)
                                  (?:fresh [x] $palindrome)
                                  ?x]
                                 []
                                 ?other)]
                             $palindrome)
                  '[a [b [d [] e] b] a])))
  #_ ;; FIXME: fixing a bug and perf issue in ?:? broke this but I cannot find the reason
  (is (= '([a b c d b a] a [c d] 123)
         (matcher '(?:letrec [palindrome
                              (| (?:? (? x symbol?)
                                      (?:fresh [x] $palindrome)
                                      ?x)
                                 ??other)]
                             [(?:as pal $palindrome) ?next])
                  '[a b c d b a 123]))))

;; It should raise a condition on no match providing me with the dict and
;; location and allow me to restart.

(deftest interesting-recusive-patterns
  (is (= [3]
         (matcher '(?:letrec [B (| 0 [?x $A])
                              A (| 0 [1 $B])]
                             [$A])
                  [[1 [3 [1 [3 0]]]]])))

  (is (= [10 1]
         (matcher '(?:letrec [A [?a 2 $B]
                              B ?b]
                             [$B $A ?a])
                  [10 [1 2 10] 1])))

  (is (= [8 4]
         (matcher '(?:letrec [A [1 2 ?a]
                              B ?b]
                             [(?:ref B) (?:ref A) 10])
                  [8 [1 2 4] 10]))))

(deftest pn
  (is (= '[a x b]
         (pattern-names '(a ((? a) (? x)) (? b) c (?? x)))))
  (is (= '[a x b]
         (pattern-names '(a ((?? a) (?? x)) (? b) c (?? x)))))
  (is (= []
         (pattern-names '(?_ ??_))))
  (is (= '[b z a]
         (pattern-names '((| (? b) 9 (? z)) (? a))))))

;; => {b {:name b, :value 1, :type ?}}

(deftest simple-patterns
  (is (= [1]
        (matcher '(a ((? b) 2 3) 1 c)
          '(a (1 2 3) 1 c))))

  (is (= [1]
        (matcher '?a 1)))

  (is (= []
        (matcher '(?:literal ?a) '?a)))

  (is (= [3 [2]]
        (matcher '((?? _ 2) ?b ??x) '(1 2 3 2))))

  (is (= [1]
        (matcher '(a ((? b) 2 3) (? b) c)
          '(a (1 2 3) 1 c))))

  (is (nil?
        (matcher '(a ((? b) 2 3) (? b) c)
          '(a (1 2 3) 2 c))))

  (is (= [[1] [2 3] 2]
        (matcher '(a ((?? a) (?? x)) (? b) c (?? x))
          '(a (1 2 3) 2 c 2 3))))
  (is (= [3 nil 4]
        (matcher [1 2 '(| [3 5] [(? a) (?? x (on-all seq)) 4] [(? a) (? a)] [(? a) (? b even?)])]
          [1 2 [3 4]])))
  (testing "syntax quoted"
    (is (= [[1] [2 3] 2]
          (matcher `(a ((?? a) (?? x)) (? b) c (?? x))
            `(a (1 2 3) 2 c 2 3))))
    (is (= [3 nil 4]
          (matcher [1 2 `(| [3 5] [(? a) (?? x (on-all seq)) 4] [(? a) (? a)] [(? a) (? b even?)])]
            [1 2 [3 4]]))))

  (testing "better function resolution/composition/etc"
    (is (= [5 9] (matcher '[?a (? b (comp even? inc *) ?a)]
                   [5 9])))

    (is (nil? (matcher '[?a (? b (comp even? inc *) ?a)]
                [5 8])))

    (is (= [5 9] (matcher '[?a (? b #(even? (inc (* %1 %2))) ?a)]
                   [5 9])))

    (is (nil? (matcher '[?a (? b #(even? (inc (* %1 %2))) ?a)]
                [5 8])))

    (is (nil? (matcher '[?a (? b (every-pred even? odd?))]
                [5 8])))

    (is (nil? (matcher '[?a (? b (every-pred even? odd?))]
                [5 9])))

    (is (= [5 8] (matcher '[?a (? b (some-fn even? odd?))]
                   [5 8])))

    (is (= [5 9] (matcher '[?a (? b (some-fn even? odd?))]
                   [5 9]))))


  (testing "apply-style restrictions using other match values as arguments"
    (is (nil?
          (matcher '[?a (? x > ?a)]
            [5 3])))
    (is (= [5 3]
          (matcher '[?a (? x < ?a)]
            [5 3])))
    (is (= [5 [3 1 5] [8 1]]
          (matcher '[?a
                     (?:* (? x <= ?a))
                     ??rest]
            [5 3 1 5 8 1])))
    (is (= [5 [] [3 1 5 8 1]]
          (matcher '[?a
                     (?:* (? x = ?a)) ;; doesn't match
                     ??rest]
            [5 3 1 5 8 1])))
    #_ ;; FIXME: this used to work until I fixed a bug in this commit in building ?:?
    (is (= [5 [5 3 1 5] [8 1]]
          ;; Use the optional matcher to capture the first value in the
          ;; sequence, and the and matcher to capture it together with the rest
          ;; of the sequence again with the restriction
          (matcher '[(& (?:? ?a ??!_)
                       (?:* (? x <= ?a)))
                     ??rest]
            [5 3 1 5 8 1]))))

  (testing "Matching the metadata map"
    (letfn [(in-range [v from to]
              ;; Return true if v is between from and to (inclusive)
              (<= from v to))]

      (testing "Matching against both a value and its metadata in one expression"
        (is (= [10 15 20]
              (matcher `(?:chain [?x] meta (?:map :from ?from :to ?to))

                (with-meta [10] {:from 15 :to 20})))))

      (testing "Using metadata in the match target to restrict the match"
        (is (= [5 20 10]
              (matcher `(& (?:chain ?_ meta (?:map :from ?from :to ?to))
                          [(? x ~in-range ?from ?to)])
                (with-meta [10] {:from 5 :to 20}))))

        (is (nil?
              (matcher `(& (?:chain ?_ meta (?:map :from ?from :to ?to))
                          [(? x ~in-range ?from ?to)])
                (with-meta [10] {:from 15 :to 20}))))

        (testing "The same can be achieved with ?:chain but it's much more verbose"
          (is (= [5 20 10]
                (matcher `(& (?:chain ?_ meta ?_ :from ?from)
                            (?:chain ?_ meta ?_ :to ?to)
                            [(? x ~in-range ?from ?to)])
                  (with-meta [10] {:from 5 :to 20})))))))))


(deftest map-matchers
  (is (= [5 20]
         (matcher `(?:map :from ?from :to ?to)
                  {:from 5 :to 20})))
  (is (= [99]
         (matcher `(?:map :struct [?a {:x :y}])
                  {:struct [99 {:x :y}]})))
  (is (nil?
       (matcher `(?:map :struct [?a {:x :y}])
                {:struct [99 {:x :zzz}]})))
  (is (= [5 5 20]
         (matcher `(?:map :from ?from :from ?x :to ?to)
                  {:from 5 :to 20}))
      "Multiple matches against a given key are fine.")
  (is (= [] (matcher `{:a 1 :b 2} {:a 1 :b 2})))
  (is (nil? (matcher '{:a 1 :b ?a} {:a 1 :b 2}))
      "Patterns are not matched within literal maps")
  (is (= [] (matcher '{:a 1 :b ?a} {:a 1 :b '?a}))
      "Patterns are not matched within literal maps. A matcher will be treated as a literal value.")
  (is (= [[:a :b]] (matcher '(?:chain ?_ keys ?k) {:a 1 :b 2}))
      "Use chain to do other types of map matches")

  (is (= [[:a :b] [1 2]]
        (matcher '(?:*map ?k ?v) {:a 1 :b 2})))
  (is (= [[:a :b] [1 2]]
        (matcher '(?:map* ?k ?v) {:a 1 :b 2})))
  (is (= [nil nil]
        (matcher '(?:*map ?k ?v) {})))

  (is (= [[:a :b] [1 2]]
        (matcher '(?:+map ?k ?v) {:a 1 :b 2})))
  (is (nil?
        (matcher '(?:+map ?k ?v) {}))))

(deftest set-matcher
  (is (= [[:b :a]]
        (matcher '(?:set ?k) #{:a :b}))))


(deftest anon-matchers
  (is (= '(1)
        (matcher '[?x (?) (?)] [1 2 3])))
  (is (= '(1)
        (matcher '[?x ?_ ?_] [1 2 3])))
  (is (= '(1)
        (matcher '[?x ??_] [1 2 3])))
  (testing "These don't match"
    (is (nil? (matcher '[?x _ _] [1 2 3])))
    (is (nil? (matcher '[?x ?_] [1 2 3])))))


(deftest other-matchers

  (is (= [nil '(1 [1 2 3] 2) nil]
         (matcher '((| ?a ??z ?b)) '(1 [1 2 3] 2))))

  (is (= [[1 2 2] [1] 2]
         (matcher '(?:as x [??aou ?1 ?1] seq) [1 2 2])))

  (is (= [[1 2 3] [1 2 3]]
         (matcher '[(?:as x ??y)] [1 2 3])))

  (testing "this is kind of pointless, but it works"
    (is (= [[1 2 3] []]
           (matcher '[(?:as x (?:? ??x ??y))] [1 2 3])))

    (is (= [[1 2 3] []]
           (matcher '[(?:as y (?:? ??x ??y))] [1 2 3])))))

(deftest modes-disabled
  (is (= 'x (var-name `?->x)))
  (binding [*disable-modes* true]
    (is (= '->x (var-name `?->x)))))

(deftest match-metadata
  (is (= [[1 2 3] "magic!"]
         (matcher '(?:chain ?obj meta ?_ :thing ?thing)
                  (with-meta [1 2 3] {:thing "magic!"})))))

(deftest test-matcher-prefix
  (is (= {'x ["t" "u"] 'y ["blog"]}
         (:var-prefixes (meta (compile-pattern '[?->t:x ?<-u:x [[?blog:y]]])))))

  (is (= {:x 1 :y 3}
         ((compile-pattern '[?->t:x ?<-u:x [[?blog:y]]])
          [1 1 [[3]]])))

  (is (= "99abc" (matcher-prefix '?->99abc:def)))
  (is (= 'def
         (var-name '(?-> abc:def))))
  (is (= "abc"
         (matcher-prefix '(?-> abc:def)))))

(deftest test-regex-matchers
  (is (= {:p "abcdef" :a "cd" :b "f"}
         ((compile-pattern '[(?:re-matches #"ab(cd)e(f)" [?p ?a ?b])])
          ["abcdef"])))
  (is (= {:x "cd" :y [["abcdef" "cd" "f"] ["abcdef" "cd" "f"]]}
         ((compile-pattern '[(?:re-seq #"ab(cd)e(f)" [[?_ ?x ??_] ??y])])
          ["abcdef aou abcdef abcdef"])))

  (is (= ["y" "z"]
         (matcher '[(?:re-matches #"x:(.)" [?_ ?x])
                    1
                    (?:re-matches #"(.):(.)" [?_ ?x ?y])
                    2]
                  ["x:y" 1 "y:z" 2])))

  (is (= '[abc/def
           "abc" def
           \c]
         (matcher '[(?:chain ?s str (?:re-matches #"(.*)/(.*)" [?_ ?ns (?:chain ?_ symbol ?name)]))
                    (?:map :name ?name
                           :ns (?:chain ?_ str ?_ reverse (\a \b ?c) (apply str) ?ns))]
                  '[abc/def
                    {:name def
                     :ns cba}]))))

(deftest test-sequence-with-optional-matches
  (is (= '{:x 1 ;; this also tests sequences with non-sequential matches
           :group-type* [nil (=> A B) nil (=> E F)]
           :name* [nil test nil test2]
           :args* [nil [a b] nil [e f]]
           :rule* [nil rule nil rule3]
           :group-type2* [(=> C D) nil (=> G H) nil]
           :rule2* [rule2 nil rule4 nil]}
         ((compile-pattern '[?x (?:* (| (?:1 ?group-type* ?x (?name* [??args*] ?rule*))
                                        (?:1 ?group-type2* ?x ?rule2*)))])
          '[1
            (=> C D) 1 rule2
            (=> A B) 1 (test [a b] rule)
            (=> G H) 1 rule4
            (=> E F) 1 (test2 [e f] rule3)])))

  (testing (str "alternate branches share the same var name, while "
                "optional matches are indexed correctly")
    (is (= '{:group-type* [(=> A B) (=> D E)]
             :name* [nil f]
             :args* [nil [g h]]
             :rule* [c i]}
           ((compile-pattern '[(?:* (? group-type*) (| (?name* [??args*] ?rule*)
                                                       ?rule*))])
            '[(=> A B) c (=> D E) (f [g h] i)])))))


(deftest combine-matcher-and-metadata-matcher
  ;; from nanopass dialect
  (let [match-value (compile-pattern '(| (? x int?) (const 1 ?a)))
        match-meta (compile-pattern '(?:map :type (| Integer Void)))
        matcher
        (compile-pattern `(& ~match-value
                             (?:all-fresh
                              (| (? _ ~not-meta?)
                                 (?:chain ?_ meta ~match-meta)))))]

    (is (matcher 123))
    (is (matcher (with-meta '(const 1 aoeu) {:type 'Void})))
    (is (not (matcher '(const 1 aoeu))))))


(deftest scoping-correctness
  (let [matcher (compile-pattern '(?a ?b
                                      (?:all-fresh [?b (?:all-fresh [?b ?c])])
                                      (?:all-fresh [?b (?:all-fresh [?b ?c])])
                                      ?c))]
    (is (= '{a {:name a, :value 1, :type ? :abbr a},
             b {:name b, :value 2, :type ? :abbr b},
             [0 b] {:name [0 b], :value 3, :type ? :abbr b},
             [0 0 b] {:name [0 0 b], :value 4, :type ? :abbr b},
             [0 0 c] {:name [0 0 c], :value 5, :type ? :abbr c},
             [1 b] {:name [1 b], :value 6, :type ? :abbr b},
             [1 0 b] {:name [1 0 b], :value 7, :type ? :abbr b},
             [1 0 c] {:name [1 0 c], :value 8, :type ? :abbr c},
             c {:name c, :value 9, :type ? :abbr c}}
           (run-matcher matcher
                        '(1 2
                            [3 [4 5]]
                            [6 [7 8]]
                            9)
                        identity)))

    (is (= '{a {:name a, :value 1, :type ? :abbr a},
             b {:name b, :value 2, :type ? :abbr b},
             [0 b] {:name [0 b], :value 3, :type ? :abbr b},
             [0 0 b] {:name [0 0 b], :value 4, :type ? :abbr b},
             [0 0 c] {:name [0 0 c], :value 5, :type ? :abbr c},
             [1 b] {:name [1 b], :value 3, :type ? :abbr b},
             [1 0 b] {:name [1 0 b], :value 4, :type ? :abbr b},
             [1 0 c] {:name [1 0 c], :value 5, :type ? :abbr c},
             c {:name c, :value 6, :type ? :abbr c}}
           (run-matcher matcher
                        '(1 2
                            [3 [4 5]]
                            [3 [4 5]]
                            6)
                        identity)))))


(deftest match-some
  (is (= {:x 2
          :y 'y
          :a [:a 1]
          :b []
          :c [3 4 'x]}
        ((compile-pattern '[?x (?:some x int? [?a ?_ (?:some y symbol? [?b ?_ ?c])])])
         [2 [:a 1 2 'y 3 4 'x]])))

  (is (= {:x 1}
        ((compile-pattern '(?:some x int?))
         [:a 1 2 3 4])))

  (is (= {:x 1 :tail [[:a] 1 [2 3 4]]}
        ((compile-pattern '(?:some x int? ?tail))
         [:a 1 2 3 4])))

  (is (= {:x 3}
        ((compile-pattern '[?x (?:some x int?)])
         [3 [:a 1 2 3 4]])))

  (is (nil?
        ((compile-pattern '[?x (?:some x int?)])
         [:a [:a 1 2 3 4]]))))

(deftest match-var-some
  (is (= {:x 2
          :y 'y
          :a [:a 1]
          :b []
          :c [3 4 'x]}
        ((compile-pattern '[?x (??:some x int? [?a ?_ (?:some y symbol? [?b ?_ ?c])])])
         [2 :a 1 2 'y 3 4 'x]))))


(deftest match-var-filter
  (is (= {:ints [2 1 2 3 4]}
        ((compile-pattern '(?:filter int? ?ints))
         [2 :a 1 2 'y 3 4 'x])))

  (is (= {:x 2, :ints [1 2 3 4]}
        ((compile-pattern '[?x (??:filter int? ?ints)])
         [2 :a 1 2 'y 3 4 'x])))
  (is (= {:x 2 :misc [:a 'y 'x]}
        ((compile-pattern '[?x (??:remove int? ?misc)])
         [2 :a 1 2 'y 3 4 'x]))))

#_
(deftest match-a-set-of-maps
  (let [r (scan-rule combine
            '[(?:as* coll
                (?:1
                  (?:map :pos ?pos)
                  (?:* (?:map :pos (| ?pos :ws)))
                  (?:map :pos ?pos)))]
            [{:text (clojure.string/join (map :text coll)) :pos pos}])]

    (is (= [{:text "My", :pos :word}
            {:text " ", :pos :ws}
            {:text "HAPPY FEET", :pos :brand-name}
            {:text " ", :pos :ws}
            {:text "Πάτοι Παπουτσιών Νο", :pos :word}
            {:text "38", :pos :number}]
          (r
            [{:text "My", :pos :word}
             {:text " ", :pos :ws}
             {:text "HAPPY", :foreign true, :pos :brand-name}
             {:text " ", :pos :ws}
             {:text "FEET", :foreign true, :pos :brand-name}
             {:text " ", :pos :ws}
             {:text "Πάτοι", :pos :word}
             {:text " ", :pos :ws}
             {:text "Παπουτσιών", :pos :word}
             {:text " ", :pos :ws}
             {:text "Νο", :pos :word}
             {:text "38", :pos :number}])))))
#_
(deftest match-a-set-of-maps-scanner
  (let [r
        (scanner {:min-len 2 :max-len 5 :extreme false :rescan false}
          (rule combine
            '[(?:as* coll
                (?:1
                  (?:map :pos ?pos)
                  (?:* (?:map :pos (| ?pos :ws)))
                  (?:map :pos ?pos)))]
            [{:text (clojure.string/join (map :text coll)) :pos pos}]))]

    (is (= [{:text "My", :pos :word}
            {:text " ", :pos :ws}
            {:text "HAPPY FEET", :pos :brand-name}
            {:text " ", :pos :ws}
            {:text "Πάτοι Παπουτσιών Νο", :pos :word}
            {:text "38", :pos :number}]
          (r
            [{:text "My", :pos :word}
             {:text " ", :pos :ws}
             {:text "HAPPY", :foreign true, :pos :brand-name}
             {:text " ", :pos :ws}
             {:text "FEET", :foreign true, :pos :brand-name}
             {:text " ", :pos :ws}
             {:text "Πάτοι", :pos :word}
             {:text " ", :pos :ws}
             {:text "Παπουτσιών", :pos :word}
             {:text " ", :pos :ws}
             {:text "Νο", :pos :word}
             {:text "38", :pos :number}])))))


(deftest rebuild-a-rule
  (let [r1 (pattern.match.predicator/with-predicates
             {'a int?}
             (rule combine
               '[?a 1 ?b]
               [a a b b]))]

    (is (= [0 0 2 2] (r1 [0 1 2])))
    (is (= [0 0 :x :x] (r1 [0 1 :x])))

    (testing "rewrite handler only"
      (let [r2 (pattern.r3.core/rebuild-rule r1 nil '[b b {b a} a a])]
        (is (= [2 2 {2 0} 0 0] (r2 [0 1 2])))
        (is (= [:x :x {:x 0} 0 0] (r2 [0 1 :x])))))

    (testing "rewrite rule only"
      (let [r3 (pattern.r3.core/rebuild-rule r1 '[?a 1 ?a:b] nil)]
        (is (= [0 0 2 2] (r3 [0 1 2])))
        (is (= [0 1 :x] (r3 [0 1 :x])) "not transformed")))

    (testing "rewrite rule only"
      (let [r4 (pattern.r3.core/rebuild-rule r1
                 (-> (get-in (meta r1) [:rule :pattern])
                   pop
                   ;; ensure be is int via predicate on a
                   (conj '?a:b))
                 '(+ a b))]
        (is (= 42 (r4 [40 1 2])))
        (is (= [40 1 :x] (r4 [40 1 :x])) "not transformed")))))



(comment
  (def rl
    (pattern/rule-list
      r))

  (pattern.types/spliceable-pattern (:match (:rule (meta r))))

  (defn zip-seq [z]
    (lazy-seq
      (when-not (zip/end? z)
        (cons (zip/node z)
          (zip-seq (zip/next z))))))

  (defn to-splice [x]
    (when (satisfies? pattern.types/SpliceablePattern x)
      (pattern.types/spliceable-pattern x)))

  (map to-splice (zip-seq (pattern.r3.combinators/rule-zipper r)))
  (map meta (zip-seq (pattern.r3.combinators/rule-zipper r))))
