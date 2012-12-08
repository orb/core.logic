(ns clojure.core.logic.clp
  (:use clojure.core.logic.protocols
        clojure.core.logic.protocols.clp
        clojure.core.logic.mk))

(defn unbound-rands [a c]
  (->> (rands c)
    flatten
    (filter #(lvar? (root-val a %)))))

(defn composeg
  ([] identity)
  ([g0 g1]
     (fn [a]
       (let [a (g0 a)]
         (and a (g1 a))))))

(defmacro composeg*
  ([g0] g0)
  ([g0 & gs]
     `(composeg
       ~g0
       (composeg* ~@gs))))

(defn addcg [c]
  (fn [a]
    (let [a (reduce (fn [a x]
                      (ext-no-check a x :clojure.core.logic/unbound))
              a (unbound-rands a c))]
      (assoc a :cs (addc (:cs a) c)))))

(defn updatecg [c]
  (fn [a]
    (assoc a :cs (updatec (:cs a) c))))

(defn remcg [c]
  (fn [a]
    (assoc a :cs (remc (:cs a) c))))

(defn runcg [c]
  (fn [a]
    (assoc a :cs (runc (:cs a) c true))))

(defn stopcg [c]
  (fn [a]
    (assoc a :cs (runc (:cs a) c false))))

(defn relevant? [c a]
  (let [id (id c)]
    (and (or ((-> a :cs :cm) id)
             (nil? id))
         (-relevant? c a))))

(defn run-constraint [c]
  (fn [a]
    (if (relevant? c a)
      (if (runnable? c a)
        ((composeg* (runcg c) c (stopcg c)) a)
        a)
      ((remcg c) a))))

;; TODO NOW: try an implementation that allows constraints
;; to run roughly in the order they normaly would. reverse
;; xcs in run-constraints, (into cq (reverse xcs)), cq should
;; be persistent list.

;; TRIED: but causes overflow errors for crypt1, and if we switch to BigInt
;; for crypt1 out of memory errors, needs more investigation

(defn fix-constraints
  "A goal to run the constraints in cq until it is empty. Of
   course running a constraint may grow cq so this function
   finds the fixpoint."
  [a]
  (loop [a a]
    (when a
      (let [cq (:cq a)]
        (if (zero? (count cq))
          (assoc a :cq nil)
          (let [c (first cq)]
            (recur
              ((run-constraint c)
               (-> a
                 (assoc :cq (subvec (:cq a) 1))
                 (assoc :cqs (disj (:cqs a) (id c))))))))))))

(defn run-constraints [xcs]
  (fn [a]
    (let [cq (:cq a)
          a  (reduce (fn [a c]
                       (queue a c))
               (assoc a :cq (or cq [])) xcs)]
     (if cq
       a
       (fix-constraints a)))))

(defn run-constraints* [xs cs ws]
  (if (or (zero? (count cs))
          (nil? (seq xs)))
    identity
    (let [xcs (constraints-for cs (first xs) ws)]
      (if (seq xcs)
        (composeg
         (run-constraints xcs)
         (run-constraints* (next xs) cs ws))
        (run-constraints* (next xs) cs ws)))))

(defn updateg [u v]
  (fn [a]
    (update a u v)))

(defn update-prefix [a ap]
  (let [l (:l a)]
    ((fn loop [lp]
       (if (identical? l lp)
         identity
         (let [[lhs rhs] (first lp)]
          (composeg
           (updateg lhs rhs)
           (loop (rest lp)))))) (:l ap))))

(defn verify-all-bound [a constrained]
  (letfn [(verify-all-bound* [a constrained]
            (when constrained
              (let [x (first constrained)]
                (if (and (lvar? x)
                         (and (lvar? (walk a x))
                              (nil? (get-attr a x :clojure.core.logic/fd)))) ;; TODO: remove hard coding of ::fd
                  (throw (Exception. (str "Constrained variable " x " without domain")))
                  (recur a (next constrained))))))]
    (verify-all-bound* a (seq constrained))))

(defn enforceable-constrained [a]
  (let [cs (:cs a)
        km (:km cs)
        cm (:cm cs)
        vs (keys km)]
    (filter (fn [v]
              (some (fn [cid]
                      (enforceable? (get cm cid)))
                    (get km v)))
            vs)))

(defn cgoal [c]
  (fn [a]
    (if (runnable? c a)
      (when-let [a (c a)]
        (if (relevant? c a)
          ((addcg c) a)
          a))
      ((addcg c) a))))

;; =============================================================================
;; defc

(def backtrack (Exception.))

(defn ground-term? [x s]
  (letfn [(-ground-term? [x s]
            (let [x (walk s x)]
              (if (lvar? x)
                (throw backtrack)
                (walk-term x
                  (fn [x]
                    (let [x (walk s x)]
                      (cond
                        (lvar? x) (throw backtrack)
                        (coll? x) (-ground-term? x s)
                        :else x)))))))]
    (try
      (-ground-term? x s)
      true
      (catch Exception e
        false))))

(defmacro defc [name args & body]
  (let [-name (symbol (str "-" name))]
   `(let [~-name (fn ~-name
                   (~args (~-name ~@args nil))
                   ([~@args id#]
                    (reify
                      ~'clojure.lang.IFn
                      (~'invoke [this# a#]
                        (let [[~@args :as args#] (map #(walk* a# %) ~args)
                              test# (do ~@body)]
                          (when test#
                            ((remcg this#) a#))))
                      clojure.core.logic.protocols.clp/IWithConstraintId
                      (~'with-id [_# id#] (~-name ~@args id#))
                      clojure.core.logic.protocols.clp/IConstraintOp
                      (~'rator [_#] '~name)
                      (~'rands [_#] (filter lvar? (flatten ~args)))
                      clojure.core.logic.protocols.clp/IReifiableConstraint
                      (~'reifyc [_# _# r#]
                        (list '~name (map #(-reify r# %) ~args)))
                      clojure.core.logic.protocols.clp/IRelevant
                      (~'-relevant? [_# s#] true)
                      clojure.core.logic.protocols.clp/IRunnable
                      (~'runnable? [_# s#]
                        (ground-term? ~args s#))
                      clojure.core.logic.protocols.clp/IConstraintWatchedStores
                      (~'watched-stores [_#] #{::subst}))))]
      (defn ~name ~args
        (cgoal (~-name ~@args))))))

