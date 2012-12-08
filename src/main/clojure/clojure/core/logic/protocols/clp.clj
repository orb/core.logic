(ns clojure.core.logic.protocols.clp)

;; =============================================================================
;; cKanren protocols

(defprotocol ISubstitutionsCLP
  (root-val [this x])
  (root-var [this x])
  (update [this x v])
  (queue [this c])
  (update-var [this x v])
  (add-attr [this x attr attrv])
  (rem-attr [this x attr])
  (get-attr [this x attro]))

;; -----------------------------------------------------------------------------
;; Constraint Store

(defprotocol IConstraintStore
  (addc [this c])
  (updatec [this c])
  (remc [this c])
  (runc [this c state])
  (constraints-for [this x ws])
  (migrate [this u v]))

;; -----------------------------------------------------------------------------
;; Generic constraint protocols

(defprotocol IRunnable
  (runnable? [c s]))

(defprotocol IWithConstraintId
  (with-id [this id]))

(extend-type Object
  IWithConstraintId
  (with-id [this id] this))

(defprotocol IConstraintId
  (id [this]))

(extend-type Object
  IConstraintId
  (id [this] nil))

(defprotocol IConstraintWatchedStores
  (watched-stores [this]))

(defprotocol IConstraintOp
  (rator [this])
  (rands [this]))

(defprotocol IRelevant
  (-relevant? [this s]))

(defprotocol IRelevantVar
  (-relevant-var? [this x]))

(defn relevant-var-c? [c]
  (instance? clojure.core.logic.protocols.clp.IRelevantVar c))

(defprotocol IReifiableConstraint
  (reifyc [this v r]))

(defn reifiable? [x]
  (instance? clojure.core.logic.protocols.clp.IReifiableConstraint x))

(defprotocol IEnforceableConstraint
  (enforceable? [c]))

(extend-type Object
  IEnforceableConstraint
  (enforceable? [x] false))

;; -----------------------------------------------------------------------------
;; force-ans support

;; TODO: this is really Mozart/OZ "distribute"

(defprotocol IForceAnswerTerm
  (-force-ans [v x]))