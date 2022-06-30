(ns pattern.r3.post-process
  (:require [pattern.r3.rule :refer [->Rule *post-processor* *identity-rule-post-processor*]]
            [pattern.util :refer [meta? deep-merge-meta]])
  (:import (pattern.r3.rule Rule)))

(defn with-post-processor
  "Change the rule to use the given post processor, replacing the old one."
  [pp ^Rule rule]
  (->Rule (.match-procedure rule) (.handler rule) (.get-values rule) pp
    (assoc-in (.metadata rule)
      [:rule :post-processor] pp)))

(defn post-processor [^Rule rule]
  (.post-processor rule))

(defn comp-post-processors
  "Compose multiple post-processors together."
  [& fs]
  (reduce (fn [c f]
            (fn [r v ov e oe]
              (let [[v e] (f r v ov e oe)]
                (c r v ov e oe))))
    (remove nil? fs)))

(defmacro use-post-processor
  "Set all rules except identity rules in this scope to use the given post
  processor."
  [pp & forms]
  `(binding [*post-processor* ~pp]
     ~@forms))

(defmacro use-post-processors
  "Set all rules, including identity rules in this scope to use the given post
  processor and identity post processor."
  [pp ident-rule-pp & forms]
  `(binding [*post-processor* ~pp
             *identity-rule-post-processor* ~ident-rule-pp]
     ~@forms))

(defn merge-metadata*
  "Merge the original value's metadata into the new value's metadata.

  If a merge strategy is attached to the new value as :rule/merge-meta, use that
  fn to do the merge. The :rule/merge-meta key will be removed from the
  resulting metadata."
  ([rule]
   (with-post-processor rule merge-metadata*))
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
   (with-post-processor rule deep-merge-metadata*))
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
  `(use-post-processor deep-merge-metadata*
     ~@forms))

(defmacro raw
  "Don't attach any post-processing to rules defined within this form"
  [& forms]
  `(use-post-processors nil nil
     ~@forms))

(defn rule-name [rule]
  (let [m (:rule (meta rule))]
    (or (:name m) (:pattern m))))

(defn mark-success
  "Capture in the env that the rule succeeded."
  [rule value _ env _]
  [value (update env :rule/success (fnil conj []) (rule-name rule))])
