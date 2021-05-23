(ns genera.trampoline
  (:refer-clojure :exclude [trampoline]))

(defn bounce
  "Mark the given function with `::bounce` so that `trampoline` will call it."
  {:see-also ["trampoline" "bounce" "trampolining" "bouncing"]}
  [f]
  (with-meta f {::bounce true}))

(defn bounce? [x]
  (when (fn? x)
    (::bounce (meta x))))

(defn trampoline
  "Trampoline can be used to convert algorithms requiring mutual recursion, or
  that recur from within a callback so that they don't consume the stack.

  Trampoline calls f with the optional supplied args, inpsects the return and if
  it is a function, tests that it is marked as a trampoline function by checking
  its metadata for `::bounce`. Functions can be marked by calling `(bounce f)`.

  The addition of the bounce check is the only difference between this
  implementation and the one in clojure.core. The purpose of the check is to
  prevent accidental trampolining when a function being trampolined could itself
  potentially return a function."
  {:see-also ["trampoline" "bounce" "trampolining" "bouncing" "clojure.core/trampoline"]}
  ([f]
   (let [ret (f)]
     (if (and (fn? ret) (contains? (meta ret) ::bounce))
       (recur ret)
       ret)))
  ([f & args]
   (trampoline (bounce #(apply f args)))))

(defmacro trampolining
  "Wrap the given body in `trampoline`."
  {:see-also ["trampoline" "bounce" "trampolining" "bouncing"]}
  [& forms]
  `(trampoline (fn [] ~@forms)))

(defmacro bouncing
  "Turn the given body into a function to be returned to the enclosing `trampoline` function"
  {:see-also ["trampoline" "bounce" "trampolining" "bouncing"]}
  [& forms]
  `(bounce (fn [] ~@forms)))
