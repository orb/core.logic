(ns clojure.core.logic.types.tabling
  (:import [java.io Writer]))

(deftype SuspendedStream [cache ansv* f]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :cache cache
      :ansv* ansv*
      :f f
      not-found))
  ISuspendedStream
  (ready? [this]
    (not= @cache ansv*)))

(defn make-suspended-stream [cache ansv* f]
  (SuspendedStream. cache ansv* f))

(defn suspended-stream? [x]
  (instance? SuspendedStream x))

(defn waiting-stream? [x]
  (vector? x))