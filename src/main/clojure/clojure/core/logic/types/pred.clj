(ns clojure.core.logic.pred
  (:import [java.io Writer]))

(defn -predc
  ([x p] (-predc x p p))
  ([x p pform]
     (reify
       Object
       (toString [_]
         (str pform))
       clojure.lang.IFn
       (invoke [this a]
         (let [x (walk a x)]
           (when (p x)
             ((remcg this) a))))
       IConstraintOp
       (rator [_] (if (seq? pform)
                    `(predc ~pform)
                    `predc))
       (rands [_] [x])
       IReifiableConstraint
       (reifyc [_ a r]
         pform)
       IRelevant
       (-relevant? [_ a] true)
       IRunnable
       (runnable? [_ a]
         (not (lvar? (walk a x))))
       IConstraintWatchedStores
       (watched-stores [this] #{::subst}))))

(defn predc
  ([x p] (predc x p p))
  ([x p pform]
     (cgoal (-predc x p pform))))