(ns pattern.matchers.nth
  (:require [pattern.types :refer [spliceable-pattern]]
            [pattern.match.core :refer :all])
  (:import (pattern.types Env)))

(set! *warn-on-reflection* true)

(defn nth-matcher [[mode idx pattern :as prop-pattern] comp-env]
  ;; It'd be good to do something more sophisticated that didn't rely on backtracking here.
  (let [matcher (compile-pattern* (list '??_ [idx pattern] '??_) comp-env)
        multi (= '??:nth mode)
        f (if (int? idx)
            (fn [data] (let [d (nth data idx ::no)]
                        (when-not (= ::no d) [[idx d]])))
            (fn [data] (map-indexed vector data)))]
    (with-meta
      (fn match-nth [data dictionary ^Env env]
        (if-let [coll (if multi data (first data))]
          (if (sequential? coll)
            (if-let [data (f coll)]
              (matcher (list data) dictionary
                (assoc env :succeed (fn [dict _n] ((.succeed env) dict (if multi (count coll) 1)))))
              (on-failure :not-vertex prop-pattern dictionary env 1 data str))
            (on-failure :not-sequential prop-pattern dictionary env 1 data str))
          (on-failure :missing prop-pattern dictionary env 0 data nil)))
      (cond-> (meta matcher)
        true (dissoc :literal `spliceable-pattern)
        multi (assoc :length (var-len 1))))))

(register-matcher '?:nth #'nth-matcher {})
(register-matcher '??:nth #'nth-matcher {})
