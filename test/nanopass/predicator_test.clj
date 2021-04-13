(ns nanopass.predicator-test
  (:require  [clojure.test :refer :all]
             [matches.nanopass.predicator :refer [per-element match-abbr make-abbr-predicator]]))

(deftest symbol-matcher
  (is (= ["?e" "?" "" "e"]
         ((match-abbr 'e) '?e)))
  (is (= ["?e*" "?" "" "e*"]
         ((match-abbr 'e) '?e*)))
  (is (= ["?e15*" "?" "" "e15*"]
         ((match-abbr 'e) '?e15*)))
  (is (= ["?e0+" "?" "" "e0+"]
         ((match-abbr 'e) '?e0+)))
  (is (nil? ((match-abbr 'e) '?ex)))
  (is (nil? ((match-abbr 'e) '?e-1)))
  (is (nil? ((match-abbr 'e) '??ex)))
  (is (nil? ((match-abbr 'e) '??->ex)))

  (is (nil? ((match-abbr 'e) '?e:1)))
  (is (= ["?e:x1" "?" "" "x1"]
         ((match-abbr 'e) '?e:x1)))

  (is (= ["?blog" "?" "" "blog"]
         ((match-abbr 'blog) '?blog)))

  (is (= ["?->blog" "?" "->" "blog"]
         ((match-abbr 'blog) '?->blog)))

  (is (= ["??!->blog:name*" "??" "!->" "name*"]
         ((match-abbr 'blog) '??!->blog:name*))))

(deftest test-abbr-predicator
  (is (= `(~'? ~'foo*1 ~symbol?)
         ((make-abbr-predicator 'x symbol?)
          '?x:foo*1)))
  (let [[matcher name pred]
        ((make-abbr-predicator 'x symbol?)
         '??x:foo*1)]
    (is (= '?? matcher))
    (is (= 'foo*1 name))
    (is (= {:per-element true} (meta pred)))
    (is (= symbol? (with-meta pred nil)))))
