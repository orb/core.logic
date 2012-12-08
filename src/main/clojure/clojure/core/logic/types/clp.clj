(ns clojure.core.logic.types.clp
  (:use clojure.core.logic.protocols
        clojure.core.logic.protocols.clp)
  (:import [java.io Writer]))

(defn var-rands [c]
  (->> (rands c)
    flatten
    (filter lvar?)
    (into [])))

(declare add-var)

;; ConstraintStore
;; -----
;; km  - mapping logic vars to constraints ids
;; cm  - mapping constraint ids to to actual constraints
;; cid - the current constraint id, an integer, incremented
;;       everytime we add a constraint to the store
;; running - set of running constraint ids

(deftype ConstraintStore [km cm cid running]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :km km
      :cm cm
      :cid cid
      :running running
      not-found))
  IConstraintStore
  (addc [this c]
    (let [vars (var-rands c)
          c (with-id c cid)
          cs (reduce (fn [cs v] (add-var cs v c)) this vars)]
      (ConstraintStore. (:km cs) (:cm cs) (inc cid) running)))
  (updatec [this c]
    (let [oc (cm (id c))
          nkm (if (relevant-var-c? c)
                (reduce (fn [km x]
                          (if-not (-relevant-var? c x)
                            (dissoc km x)
                            km))
                        km (var-rands oc))
                km)]
      (ConstraintStore. nkm (assoc cm (id c) c) cid running)))
  (remc [this c]
    (let [vs (var-rands c)
          ocid (id c)
          nkm (reduce (fn [km v]
                        (let [vcs (disj (get km v) ocid)]
                          (if (empty? vcs)
                            (dissoc km v)
                            (assoc km v vcs))))
                      km vs)
          ncm (dissoc cm ocid)]
      (ConstraintStore. nkm ncm cid running)))
  (runc [this c state]
    (if state
      (ConstraintStore. km cm cid (conj running (id c)))
      (ConstraintStore. km cm cid (disj running (id c)))))
  (constraints-for [this x ws]
    (when-let [ids (get km x)]
      (filter #((watched-stores %) ws) (map cm (remove running ids)))))
  (migrate [this u v]
    (let [ucs (km u)
          vcs (km v)
          nkm (assoc (dissoc km u) v (into vcs ucs))]
      (ConstraintStore. nkm cm cid running)))
  clojure.lang.Counted
  (count [this]
    (count cm)))

(defn add-var [cs x c]
  (when-not (lvar? x)
    (throw (Error. (str "constraint store assoc expected logic var key: " x))))
  (let [cm (:cm cs)
        km (:km cs)
        cid (:cid cs)
        nkm (update-in km [x] (fnil (fn [s] (conj s cid)) #{}))
        ncm (assoc cm cid c)]
    (ConstraintStore. nkm ncm cid (:running cs))))

(defn make-cs []
  (ConstraintStore. {} {} 0 #{}))