(ns pattern.r3.post-process
  (:require [pattern.r3.rule :refer [->Rule rule-name
                                     *post-processor* *identity-rule-post-processor*]]
            [pattern.util :refer [meta?]])
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

(defn post-processors
  "Get the currently active default post-processors"
  []
  [*post-processor* *identity-rule-post-processor*])

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

(defmacro merge-metadata
  "Attach a post processor that will merge the original value's metadata into
  the new value's metadata.

  If a merge strategy is attached to the new value as :rule/merge-meta, use that
  fn to do the merge. The :rule/merge-meta key will be removed from the
  resulting metadata."
  [& forms]
  `(use-post-processors merge-metadata* merge-metadata*
     ~@forms))

(defmacro raw
  "Don't attach any additional post-processing to rules defined within this form

  If post processors are attached within the raw form, they will remain."
  [& forms]
  `(use-post-processors nil nil
     ~@forms))

(defn mark-success
  "Capture in the env that the rule succeeded."
  [rule value _ env _]
  [value (update env :rule/success (fnil conj []) (rule-name rule))])
