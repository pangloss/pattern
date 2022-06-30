(ns pattern.r3.post-process
  (:require [pattern.r3.rule :refer [->Rule *post-processor* *identity-rule-post-processor*]]
            [pattern.util :refer [meta? deep-merge-meta]]))

(defn set-post-processor [rule pp]
  (->Rule (.match-procedure rule) (.handler rule) (.get-values rule) (.post-process rule) (.metadata rule)))

(defn merge-metadata*
  "Merge the original value's metadata into the new value's metadata.

  If a merge strategy is attached to the new value as :rule/merge-meta, use that
  fn to do the merge. The :rule/merge-meta key will be removed from the
  resulting metadata."
  ([rule]
   (set-post-processor rule merge-metadata*))
  ([rule value orig-value env orig-env]
   (if (or (identical? value orig-value) (not (meta? value)))
     [value env]
     (if-let [orig-meta (meta orig-value)]
       (if-let [m (meta value)]
         (if-let [mm (:rule/merge-meta m)]
           [(with-meta value (mm orig-meta (dissoc m :rule/merge-meta))) env]
           [(with-meta value (merge orig-meta m)) env])
         [(with-meta value orig-meta) env])
       [value env]))))

(defn deep-merge-metadata*
  "Recursively merge as much of the metadata attached to the orig-value as
  possible into the new value.

  If a merge strategy is attached to the new value as :rule/merge-meta, use that
  fn to do the merge at each level. If :rule/merge-meta is false, pass the new
  value through unchanged. The :rule/merge-meta key will be removed from the
  resulting metadata."
  ([rule]
   (set-post-processor rule deep-merge-metadata*))
  ([rule value orig-value env orig-env]
   (if (identical? value orig-value)
     [value env]
     (let [merge-meta (:rule/merge-meta (meta value) merge)]
       (if merge-meta
         [(deep-merge-meta orig-value (vary-meta value dissoc :rule/merge-meta) merge-meta)
          env]
         [(if (meta? value)
            (vary-meta value dissoc :rule/merge-meta)
            value)
          env])))))

(defmacro deep-merge-metadata
  "All rules defined within this form will perform a deep metadata merge. All
  metadata recursively found in the matched data will be merged into the result
  data. The idea is to preserve metadata in compiler transformations, etc."
  [& forms]
  `(binding [*post-processor* deep-merge-metadata*]
     ~@forms))

(defmacro raw
  "Don't attach any post-processing to rules defined within this form"
  [& forms]
  `(binding [*post-processor* nil
             *identity-rule-post-processor* nil]
     ~@forms))
