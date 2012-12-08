(ns clojure.core.logic.protocols.fd)

;; -----------------------------------------------------------------------------
;; Finite domain protocol types

(defprotocol IInterval
  (lb [this])
  (ub [this]))

(defprotocol IMemberCount
  (member-count [this]))

(defprotocol IIntervals
  (intervals [this]))

(defprotocol IFiniteDomain
  (domain? [this]))

(extend-protocol IFiniteDomain
  nil
  (domain? [x] false)

  Object
  (domain? [x] false))

(defprotocol ISortedDomain
  (drop-one [this])
  (drop-before [this n])
  (keep-before [this n]))

(defprotocol ISet
  (member? [this n])
  (disjoint? [this that])
  (intersection [this that])
  (difference [this that]))