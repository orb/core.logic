(ns clojure.core.logic.protocols.tree)

;; -----------------------------------------------------------------------------
;; Tree Constraints

(defprotocol ITreeConstraint
  (tree-constraint? [this]))

(extend-type Object
  ITreeConstraint
  (tree-constraint? [this] false))

(defprotocol IPrefix
  (prefix [this]))

(defprotocol IWithPrefix
  (with-prefix [this p]))