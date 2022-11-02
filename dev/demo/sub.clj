(ns demo.sub
  (:require [pattern :refer [sub]]))


(let [a 1 b [2]]
  (sub (?:map :a ?a :b ?b :c :c :d [?a ?b])))

(let [a* [99]
      b* []
      c* [1 2]
      xs 5
      ys 9]
  [(sub (* ??a* ??b* ??c* (sqrt (* ?xs ?ys))))
   (sub (?:* ?c*))
   (sub (?:+ ?c*))
   (sub (?:? ?c* ?c*))
   (sub (?:1 ?c* ?c*))
   (sub (?:? ??c*))
   (sub (?:1 ??c*))
   (sub (?:? ?xs ?ys))
   (sub (?:1 ?xs ?ys))
   (sub ??c*)
   (sub ?c*)])


(let [a 'a b 'b x true c ['C 'C]]
  (sub [?a ?b (| ?x 3 (??-> c)) 1 2 3 [3 4]]))

(let [a 'a b 'b x false c ['C 'C]]
  (sub [?a ?b (| ?x 3 (??-> c)) 1 2 3 [3 4]]))

(let [a :a b :b x nil c [:C :C]]
  (sub [?a ?b (| ?x (??-> c)) 1 2 3 [3 4]]))


(let [i 1 k :x]
  [(sub [(?:if keyword? :x "not keyword")])
   (sub (?:if keyword? :x "not keyword"))])

(let [a true]
  [(sub [... (?:when keyword? :x 1 2 3 ?a)])
   ;; when returning a group it only returns the first element.
   (sub (?:when keyword? :x 1 2 3 ?a))])

(let [i 1 k :kw]
  [(sub [(?:if int? ?i ?k)])
   (sub [(?:if symbol? ?i ?k)])
   (sub [(?:if int? ?i)])
   (sub [(?:if symbol? ?i)])
   (sub [(?:when int? ?i)])
   (sub [(?:when symbol? ?i)])
   (sub [(?:when int? ?i 2 3)])
   (sub [(?:when symbol? ?i 2 3)])])

;; What a weird behaviour, but it is consistent and correct, I think!. Group to
;; a pred applies it as arguments...
(let [m {:a 1 :b 2} k :a]
  [(sub [:x (?:if get (?:? ?m ?k) (?:? 111 999))])
   (let [k :c]
     [(sub [:x (?:if get (?:? ?m ?k) (?:? 111 999))])
      (sub [:x (?:if get (?:? ?m ?k))])])])

;;with pre-insertion transformation
(let [a [1 2 3]]
  (sub inc (+ (?:* ?a ?<-a))))
