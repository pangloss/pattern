(ns predicator-test
  (:require  [clojure.test :refer :all]
             [matches :refer [compile-pattern]]
             [matches.match.predicator :refer [match-abbr apply-predicator make-abbr-predicator]]))

(deftest symbol-matcher
  (is (= ["?e" "?" "" "" "e"]
         ((match-abbr 'e) '?e)))
  (is (= ["?e*" "?" "" "" "e*"]
         ((match-abbr 'e) '?e*)))
  (is (= ["?e15*" "?" "" "" "e15*"]
         ((match-abbr 'e) '?e15*)))
  (is (= ["?e0+" "?" "" "" "e0+"]
         ((match-abbr 'e) '?e0+)))
  (is (nil? ((match-abbr 'e) '?ex)))
  (is (nil? ((match-abbr 'e) '?e-1)))
  (is (nil? ((match-abbr 'e) '??ex)))
  (is (nil? ((match-abbr 'e) '??->ex)))

  (is (nil? ((match-abbr 'e) '?e:1)))
  (is (= ["?e:x1" "?" "" "e:" "x1"]
         ((match-abbr 'e) '?e:x1)))

  (is (= ["?blog" "?" "" "" "blog"]
         ((match-abbr 'blog) '?blog)))

  (is (= ["?->blog" "?" "->" "" "blog"]
         ((match-abbr 'blog) '?->blog)))

  (is (= ["??!->blog:name*" "??" "!->" "blog:" "name*"]
         ((match-abbr 'blog) '??!->blog:name*))))

(deftest test-abbr-predicator
  (is (= `(~'? ~'x:foo*1 ~symbol?)
         (apply-predicator
          (make-abbr-predicator 'x symbol?)
          '?x:foo*1)))
  (let [[matcher name pred]
        (apply-predicator
         (make-abbr-predicator 'x symbol?)
         '??x:foo*1)]
    (is (= '?? matcher))
    (is (= 'x:foo*1 name))
    (is (= symbol? (with-meta pred nil)))))

#_ ;; TODO
(deftest test-possible-attrs
  ;; Note that the name x:_ is treated as anonymous, so it doesn't appear in
  ;; var-names, var-modes or var-prefixes.
  (is (= '{b a, a*1 a, astaou astaou, xao aou, def abc}
       (possible-abbrs (compile-pattern '(?->x:_ ?a:b ?a*1 ?astaou ??aou:xao (? abc:def)))))))
