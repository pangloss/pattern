(ns compiler-course.pass07-expose-allocation
  (:require [compiler-course.r1-allocator :refer [liveness to-graph allocate-registers*
                                                  caller-saved-registers callee-saved-registers
                                                  var-locations with-allocated-registers]]
            [compiler-course.dialects :refer [r1-keyword?]]
            [matches.nanopass.dialect :refer [all-dialects =>:to show-parse]]
            [matches :refer [descend in gennice niceid directed on-subexpressions rule rule-list rule-list!
                             descend-all sub success subm rule-simplifier matcher
                             => dialects validate ok ok?]]
            [matches.types :refer [child-rules]]
            [clojure.string :as str]
            [compiler-course.pass06-add-types :refer [add-types]]))



;; Expand the inner workings of (vector ...)

(defmacro m! []
  `(meta (:rule/datum ~'%env)))

(def expose-allocation
  (dialects
   (=> Typed AllocTyped)
   (rule-simplifier
    (rule '(vector ??e*)
          (let [t (::type (m!))]
            (subm (vector> ~t [] [??e*] [~@(rest t)]) (m!))))
    (rule '(vector> ?type ?names [?e ??e*] [?t ??t*])
          (let [n (with-meta (gennice 'entry) {::type t})
                ;; building names in reverse
                m (m!)
                names (conj names n)]
            (subm (let ([?n ?e])
                    ~(subm (vector> ?type ?names [??e*] [??t*]) m))
                  m)))
    (rule '(vector> ?type ?names [] [])
          (let [len (count names)
                ;; types will be inferred by add-types below.
                m (m!)
                v (with-meta (gennice 'vector) m)
                _ (gennice '_)
                bytes (* 8 (inc len))]
            (subm
             (let ([?_ ~(add-types
                         (sub (if (< (+ (global-value free_ptr) ?bytes)
                                     (global-value fromspace_end))
                                (void)
                                (collect ?bytes))))])
               ~(subm
                 (let ([?v ~(subm (allocate ?len ?type) m)])
                   ~(subm (vector< ?v ?names) m))
                 m))
             m)))
    (rule '(vector< ?v [??n* ?n])
          ;; using names in reverse, so n* count is the vector position
          (let [idx (count n*)
                m (m!)
                _ (with-meta (gennice '_) {::type 'Void})]
            (subm (let ([?_ ~(subm (vector-set! ?v ?idx ?n)
                                   {::type 'Void})])
                    ~(subm (vector< ?v [??n*]) m))
                  m)))
    (rule '(vector< ?v [])
          (with-meta v (m!))))))