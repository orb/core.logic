(ns clojure.core.logic.tree)

(defn prefix-s [s <s]
  (letfn [(prefix* [s <s]
            (if (identical? s <s)
              nil
              (cons (first s) (prefix* (rest s) <s))))]
    (when-let [p (prefix* (:l s) (:l <s))]
      (with-meta p {:s s}))))

;; TODO: unify should return the prefix sub, then can eliminate l - David

(defn prefix-subsumes? [p pp]
  (let [s (-> p meta :s)
        sp (reduce (fn [s [lhs rhs]]
                     (unify s lhs rhs))
                   s pp)]
    (when sp
      (identical? s sp))))

(defn recover-vars [p]
  (loop [p (seq p) r #{}]
    (if p
      (let [[u v] (first p)]
        (if (lvar? v)
          (recur (next p) (conj r u v))
          (recur (next p) (conj r u))))
      r)))

(declare normalize-store)

(defn !=c
  ([p] (!=c p nil))
  ([p id]
     (reify
       clojure.lang.IFn
       (invoke [this a]
         (if-let [ap (reduce (fn [a [u v]]
                               (when a (unify a u v)))
                             a p)]
           (when-let [p (prefix-s ap a)]
             ((normalize-store (with-prefix this p)) a))
           ((remcg this) a)))
       ITreeConstraint
       (tree-constraint? [_] true)
       IWithConstraintId
       (with-id [_ id] (!=c p id))
       IConstraintId
       (id [_] id)
       IPrefix
       (prefix [_] p)
       IWithPrefix
       (with-prefix [_ p] (!=c p id))
       IEnforceableConstraint
       (enforceable? [_] false)
       IReifiableConstraint
       (reifyc [this v r]
         (let [p* (walk* r (map (fn [[lhs rhs]] `(~lhs ~rhs)) p))]
           (if (empty? p*)
             '()
             (let [p* (filter (fn [[lhs rhs]]
                                (not (or (var? lhs)
                                         (var? rhs))))
                              p*)]
               `(~'!= ~@(first p*))))))
       IConstraintOp
       (rator [_] `!=)
       (rands [_] (seq (recover-vars p)))
       IRunnable
       (runnable? [this s]
         (some #(not= (walk s %) %) (recover-vars p)))
       IRelevant
       (-relevant? [this s]
         (not (empty? p)))
       IRelevantVar
       (-relevant-var? [this x]
         ((recover-vars p) x))
       IConstraintWatchedStores
       (watched-stores [this] #{::subst}))))

(defn normalize-store [c]
  (fn [a]
    (let [p (prefix c)
          cid (id c)
          cs (:cs a)
          cids (->> (seq (recover-vars p))
                    (mapcat (:km cs))
                    (remove nil?)
                    (into #{}))
          neqcs (->> (seq cids)
                     (map (:cm cs))
                     (filter tree-constraint?)
                     (remove #(= (id %) cid)))]
      (loop [a a neqcs (seq neqcs)]
        (if neqcs
          (let [oc (first neqcs)
                pp (prefix oc)]
            (cond
             (prefix-subsumes? pp p) ((remcg c) a)
             (prefix-subsumes? p pp) (recur (assoc a :cs (remc cs oc)) (next neqcs))
             :else (recur a (next neqcs))))
          ((updatecg c) a))))))

(defn !=
  "Disequality constraint. Ensures that u and v will never
   unify. u and v can be complex terms."
  [u v]
  (fn [a]
    (if-let [ap (unify a u v)]
      (let [p (prefix-s ap a)]
        (when-not (empty? p)
          ((cgoal (!=c p)) a)))
      a)))
