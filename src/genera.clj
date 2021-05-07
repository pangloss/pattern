(ns genera
  (:refer-clojure :exclude [trampoline])
  (:require genera.macros
            genera.core
            genera.trampoline
            potemkin))


(potemkin/import-vars
 (genera.macros defgenera
                defgenera*
                defgenera=
                defgen
                defgen*
                defgen!
                defgen=
                defmethod*
                defmethod!
                defmethod=)
 (genera.core specialize find-handler)
 (genera.trampoline trampoline bounce
                    trampolining bouncing))
