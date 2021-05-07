(ns genera.types)

(defprotocol IRule
  (handler-for-args [rule args]))

(defprotocol Store
  (get-handler [s args])
  (get-handler-with-pred [s pred args])
  (with-handler [s applicability handler])
  (get-default-handler [s]))

(defprotocol IGenericProcedure
  (define-handler [p applicability handler]))

(defrecord Trie [value edges])

(defrecord Edge [ev trie])
