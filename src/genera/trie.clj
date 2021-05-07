(ns genera.trie
  (:require [genera.types :refer [->Trie ->Edge]])
  (:import (genera.types Trie Edge)))

(defn make-trie []
  (->Trie nil []))

(defn set-path-value [trie path value]
  (if-let [path-item (first path)]
    (let [old-edge (some (fn [^Edge edge]
                           (when (= (.ev edge) path-item)
                             edge))
                         (:edges trie))
          child (set-path-value (:trie old-edge)
                                (rest path)
                                value)
          new-edge (if old-edge
                     (assoc old-edge :trie child)
                     (->Edge path-item child))]
      (cond (and trie old-edge)
            (update trie :edges (partial replace {old-edge new-edge}))
            trie
            (update trie :edges conj new-edge)
            :else
            (->Trie nil [new-edge])))
    (if trie
      (assoc trie :value value)
      (->Trie value []))))

(defn find-all-edges [^Trie trie feature]
  (->> (.edges trie)
       (keep (fn [^Edge edge]
               (when ((.ev edge) feature)
                 (.trie edge))))))

(defn get-matching-tries [trie features]
  (loop [tries [trie]
         features features]
    (if (seq features)
      (let [feature (first features)]
        (recur (mapcat (fn [trie]
                         (find-all-edges trie feature))
                       tries)
               (rest features)))
      tries)))

(defn get-all-values [trie features]
  (->> (get-matching-tries trie features)
       (keep (fn [^Trie t] (.value t)))))


(defn find-all-edges-with-pred [^Trie trie pred feature]
  (->> (.edges trie)
       (keep (fn [^Edge edge]
               (when (pred (.ev edge) feature)
                 (.trie edge))))))

(defn get-matching-tries-with-pred [trie pred features]
  (loop [tries [trie]
         features features]
    (if (seq features)
      (let [feature (first features)]
        (recur (mapcat (fn [trie]
                         (find-all-edges-with-pred trie pred feature))
                       tries)
               (rest features)))
      tries)))

(defn get-all-values-with-pred [trie pred features]
  (->> (get-matching-tries-with-pred trie pred features)
       (keep (fn [^Trie t] (.value t)))))

(defn get-a-value-with-pred [trie pred features]
  (first (get-all-values-with-pred trie pred features)))

(defn get-a-value-by-filtering [trie features]
  (first (get-all-values trie features)))

(defn try-edge [^Edge edge feature succeed fail]
  (if ((.ev edge) feature)
    (succeed (.trie edge) fail)
    (fail)))

(defn try-edges [edges feature succeed fail]
  (if (seq edges)
    (try-edge (first edges)
              feature
              succeed
              (fn []
                (try-edges (next edges) feature succeed fail)))))

(defn get-a-value-by-searching [trie features]
  (letfn [(search [^Trie trie features succeed fail]
            (if (seq features)
              (try-edges (.edges trie)
                         (first features)
                         (fn [trie* fail*]
                           ;; no TCO happening here...
                           (search trie* (rest features) succeed fail*))
                         fail)
              (if (.value trie)
                (succeed (.value trie) fail)
                (fail))))]
    (search trie
            features
            (fn [value fail] value)
            (fn [] (throw (ex-info "Unable to match features" {:features features}))))))

(def get-a-value get-a-value-by-searching)

(comment
  (-> (set-path-value nil [1 2 3] :x)
      (set-path-value [1 2 4] :y)
      (set-path-value [2] :z)
      (set-path-value [1] :w)
      (set-path-value [1] :W))

  (-> (set-path-value nil [int? symbol?] :x)
      (set-path-value [int? string?] :y)
      (get-a-value [2 'hi]))

  (-> (set-path-value nil [int? symbol?] :x)
      (set-path-value [int? string?] :y)
      (set-path-value [pos-int? string?] :z)
      (get-a-value-by-filtering [2 "x"]))

  ,)
