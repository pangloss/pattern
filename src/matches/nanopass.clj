(ns matches.nanopass
  (:require [matches.r2.rewrite :refer [sub]]
            [matches.r2.combinators :refer :all]
            [matches.r2.core :refer [rule]]
            [matches.types :refer [->MetaBox ->ValuesBox]])
  (:import [clojure.lang IMeta IObj]
           matches.types.ValuesBox))

;;; WIP:

(defn force-meta [box x f & m]
  (if (instance? IObj x)
    (apply vary-meta x f m)
    (apply vary-meta ((or box ->MetaBox) x) f m)))

(defn tag
  ([x k v]
   (when x
     (force-meta nil x assoc k v)))
  ([x k v & more]
   (when x
     (apply force-meta nil x assoc k v more))))

;; return/values seems no better than just using a vector.
#_#_
(defn return [obj extra & extras]
  (force-meta ->ValuesBox obj assoc ::return (cons extra extras)))

(defn values
  ([obj]
   (cons (if (instance? ValuesBox obj)
           (:value obj)
           (if (instance? IMeta obj)
             (vary-meta obj dissoc ::return)
             obj))
         (::return (meta obj)))))

(defn immediate? [x]
  (= :immediate (::tag (meta x))))

(def ^:dynamic *from-lang*)
(def ^:dynamic *from-type*)
(def ^:dynamic *to-lang*)
(def ^:dynamic *to-type*)

(defmacro scope
  ([[from-lang -> to-lang to-type] & body]
   (assert (= '-> ->))
   `(binding [*from-lang* '~from-lang
              *to-lang* '~to-lang
              *to-type* '~to-type]
      ~@body)))

(defn as
  ([type value]
   (when-let [pred (::pred (meta type))]
     (assert (pred value)))
   (tag value ::lang *to-lang* ::tag type))
  ([lang type value]
   (when-let [pred (::pred (meta type))]
     (assert (pred value)))
   (tag value ::lang lang ::tag type)))

(defn to
  ([value]
   (tag value ::lang *to-lang* ::tag *to-type*))
  ([to-type value]
   (tag value ::lang *to-lang* ::tag to-type))
  ([to-lang to-type value]
   (tag value ::lang to-lang ::tag to-type)))

(defn from [from-type value rules]
  `(when (= from-type (::tag (meta value)))
     (as *to-lang* *to-type*
         ~@rules)))

(meta
 (scope [L1 -> L2 Expr]
        [] #_(nanopass-case '(+ 1 (+ a 1)))))

(defmacro type-rules [[from -> to] & rules]
  ;; FIXME: implement this
  (vec rules))

(comment
  ;; rules like this
  ;;   (Triv : Triv (x) -> Triv ()
  ;;         [,x (var x)]
  (defn eliminate-simple-moves [ir]
    (scope [Lflat-funcs -> lflat-funcs]
           ;; group 1
           (directed
            (rule-list
             (type-rules [Triv ->] ;; does not tag the output
                         (rule '?x   (var x))
                         (rule '?int int))
             ;; group 2
             (type-rules [Triv -> Triv] ;; filter input, tag output
                         (rule '?x   (var x))
                         (rule '?int int))
             ;; group 3
             (type-rules [-> Triv] ;; don't filter input, do tag output
                         (rule '?x   (var x))
                         (rule '?int int))))))
  ;; to the following:
  (defn eliminate-simple-moves [ir]
    (scope [Lflat-funcs -> lflat-funcs]
           (directed
            (rule-list
             [;; group 1
              (rule '(& (? _ triv?) ?x)   (var x))
              (rule '(& (? _ triv?) ?int) int)
              ;; group 2
              (rule '(& (? _ triv?) ?x)   (tag (var x) ::lang 'Lflat-funcs ::nt 'Triv))
              (rule '(& (? _ triv?) ?int) (tag int ::lang 'Lflat-funcs ::nt 'Triv))
              ;; group 3
              (rule '?x   (tag (var x) ::lang 'Lflat-funcs ::nt 'Triv))
              (rule '?int (tag int ::lang 'Lflat-funcs ::nt 'Triv))])))))


#_
(defmacro nc [name | from-type bindings -> to-type & rules]
  `(fn ~name ~bindings
     (or (to ~to-type
             (from ~from-type
                   ~(first bindings)
                   ~rules)))))



(defn make-var [x]
  (vary-meta x assoc ::tag :var))

(defn make-prim [x]
  (vary-meta x assoc ::tag :prim))

;; This one isn't turning out too great. The craziness of scheme is not helping, either...
(defn convert-complex-datum [ir]
  (scope
   [Lsrc -> Ldatum]
   (letfn [(build-let [x* e* e]
             (if (empty? x*)
               e
               (sub (let ((?:* [?x* ?e*])) ?e))))
           (build-begin [e* e]
             (if (empty? e*)
               e
               (sub (begin ??e* ?e))))
           (build-lambda [x* e]
             (sub (lambda (??x*) ?e)))
           (convert-datum [d]
             (cond (list? d)
                   (let [var-a (make-var 'tmp-a)
                         var-d (make-var 'tmp-d)
                         e-a   (convert-datum (first d))
                         e-d   (convert-datum (second d))]
                     (build-let [var-a var-d] [e-a e-d]
                                (sub (~(make-prim 'cons) ?var-a ?var-d))))
                   (vector? d)
                   (let [n  (count d)
                         i* (range n)
                         t* (map #(make-var (symbol (format "tmp-%s" %))) i*)
                         e* (map convert-datum d)
                         t  (make-var 'tmp-v)]
                     (build-let [t]
                                [(sub (~(make-prim 'make-vector) ?n))]
                                (build-begin (map (fn [ti i] (sub (~(make-prim 'vector-set!) ?t ?i ?ti))))
                                             t)))
                   (immediate? d) (sub (quote ?d))))]
     #_
     (nc Expr | Expr [ir datum-var* datum-e*] -> Expr
         (rule '(quote ?d)
               (if (immediate? d)
                 ir
                 (let [var (make-var 'tmp)
                       e   (convert-datum d)]
                   (return var (conj datum-var* var) (conj datum-e* e)))))
         ;; FIXME: it's totally unclear how the original traverses the entire
         ;; expression tree. There is no ,[e*] anywhere which I thought was the
         ;; signal to traverse deeper, nor is there an explicit call to (Expr ...)
         ;; on any subexpression, which I thought was the only other way... For now
         ;; I haven't implemented recursion here even though it seems necessary

         (let [[ir datum-var* datum-e*] (values (Expr ir [] []))]
           (build-let datum-var* datum-e* ir))))))

#_
(defn remove-anon-lambda [ir]
  (scope [Lno-assign -> LSanitized]
         (nc Expr | Expr [ir {:keys [needs-name? maybe-name] :or {needs-name? true}}] -> Expr
             ;; rule needs to insert predicates for things like ?f -> (? f lambda-expr?)
             (rule '?f
                   (if needs-name?
                     (let [t (make-var (or maybe-name 'anon))]
                       (sub (letrec ([?t (Lambda ?f)]) ?t)))
                     (as 'Lambda f)))
             (rule '(let ((?:* [?x* ?e*])) ?e)
                   (let [e* (map (fn [x e] (Expr e false x)) x* e*)
                         e (Expr e true maybe-name)]
                     (sub (let ((?:* [?x* ?e*])) ?e)))))))
