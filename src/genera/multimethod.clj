(ns genera.multimethod
  (:refer-clojure :rename {defmethod core-defmethod}))


(defn fn-for-dispatch-val [multimethod dispatch-val]
  (.getMethod multimethod dispatch-val))

(defn dispatch-val [multimethod & args]
  (apply (.dispatchFn multimethod) args))

(defn dispatch-fn [multimethod & args]
  (fn-for-dispatch-val multimethod (apply dispatch-val multimethod args)))

(defn dispatch-val-resolved [multimethod & args]
  (get (clojure.set/map-invert (.getMethodTable multimethod))
       (apply dispatch-fn multimethod args)))

(def instrument-defmethod
  (atom
   ;; FIXME: find cljs-friendly alternative
   (= (System/getProperty "genera.instrument_defmethod") "true")))

(def generic-call-id (atom 0))
(def ^:dynamic *generic-call-chain* [])
(def ^:dynamic *generic-call-tap?* (constantly false))
(def ^:dynamic *on-generic-call* (constantly nil))

(defmacro defmethod [multifn dispatch-val & fn-tail]
  (if @instrument-defmethod
    `(let [call-info# {:dispatch ~dispatch-val :name (if (dispatch-val-resolved ~multifn :name)
                                                       (~multifn :name)
                                                       '~multifn)}]
       (prn "using instrumentation")
       (core-defmethod ~multifn ~dispatch-val ~@(butlast fn-tail)
                       (let [call-id# (swap! generic-call-id inc)
                             call-info# (assoc call-info# :id call-id# :parent-id (:id (last *generic-call-chain*)))
                             tap?# (*generic-call-tap?* call-info#)]
                         (when tap?#
                           (*on-generic-call*
                            (assoc (try (assoc call-info#
                                               :args ~(first fn-tail)
                                               :dispatch-with (dispatch-val ~multifn ~@(first fn-tail)))
                                        ;; If the function destructures I'm not going to try to figure that out.
                                        (catch Exception e# call-info#))
                                   :chain *generic-call-chain*)))
                         (let [result#
                               (binding [*generic-call-chain* (conj *generic-call-chain* call-info#)]
                                 ~(last fn-tail))]
                           (when tap?#
                             (*on-generic-call* (assoc call-info# :result result#)))
                           result#))))
    `(core-defmethod ~multifn ~dispatch-val ~@fn-tail)))

