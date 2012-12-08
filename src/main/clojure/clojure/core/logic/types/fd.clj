(ns clojure.core.logic.types.fd
  (:use clojure.core.logic.protocols.fd)
  (:require [clojure.set :as set])
  (:import [java.io Writer]))

;; FiniteDomain
;; -----
;; wrapper around Clojure sorted sets. Used to represent small
;; domains. Optimization when interval arithmetic provides little
;; benefit.
;;
;; s - a sorted set
;; min - the minimum value, an optimization
;; max - the maximum value, an optimization

(deftype FiniteDomain [s min max]
  Object
  (equals [this that]
    (if (finite-domain? that)
      (if (= (member-count this) (member-count that))
        (= s (:s that))
        false)
      false))
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :s s
      :min min
      :max max
      not-found))
  IMemberCount
  (member-count [this] (count s))
  IInterval
  (lb [_] min)
  (ub [_] max)
  ISortedDomain
  (drop-one [_]
    (let [s (disj s min)
          c (count s)]
      (cond
       (= c 1) (first s)
       (> c 1) (FiniteDomain. s (first s) max)
       :else nil)))
  (drop-before [_ n]
    (apply domain (drop-while #(< % n) s)))
  (keep-before [this n]
    (apply domain (take-while #(< % n) s)))
  IFiniteDomain
  (domain? [_] true)
  ISet
  (member? [this n]
    (if (s n) true false))
  (disjoint? [this that]
    (cond
     (integer? that)
       (if (s that) false true)
     (instance? FiniteDomain that)
       (cond
         (< max (:min that)) true
         (> min (:max that)) true
         :else (empty? (set/intersection this (:s that))))
     :else (disjoint?* this that)))
  (intersection [this that]
    (cond
     (integer? that)
       (when (member? this that) that)
     (instance? FiniteDomain that)
       (sorted-set->domain (set/intersection s (:s that)))
     :else
       (intersection* this that)))
  (difference [this that]
    (cond
     (integer? that)
       (sorted-set->domain (disj s that))
     (instance? FiniteDomain that)
       (sorted-set->domain (set/difference s (:s that)))
     :else
       (difference* this that)))
  IIntervals
  (intervals [_] (seq s)))

(defn finite-domain? [x]
  (instance? FiniteDomain x))

(defn sorted-set->domain [s]
  (let [c (count s)]
    (cond
     (zero? c) nil
     (= c 1) (first s)
     :else (FiniteDomain. s (first s) (first (rseq s))))))

(defn domain
  "Construct a domain for assignment to a var. Arguments should 
   be integers given in sorted order. domains may be more efficient 
   than intervals when only a few values are possible."
  [& args]
  (when (seq args)
    (sorted-set->domain (into (sorted-set) args))))

(defmethod print-method FiniteDomain [x ^Writer writer]
  (.write writer (str "<domain:" (string/join " " (seq (:s x))) ">")))

(declare interval?)

(defmacro extend-to-fd [t]
  `(extend-type ~t
     IMemberCount
     (~'member-count [this#] 1)
     IInterval
     (~'lb [this#] this#)
     (~'ub [this#] this#)
     (~'bounds [this#] (pair this# this#))
     ISortedDomain
     (~'drop-one [this#]
       nil)
     (~'drop-before [this# n#]
       (when (>= this# n#)
         this#))
     (~'keep-before [this# n#]
       (when (< this# n#)
         this#))
     IFiniteDomain
     (~'domain? [this#] true)
     ISet
     (~'member? [this# that#]
       (if (integer? that#)
         (= this# that#)
         (member? that# this#)))
     (~'disjoint? [this# that#]
       (if (integer? that#)
         (not= this# that#)
         (disjoint? that# this#)))
     (~'intersection [this# that#]
       (cond
        (integer? that#) (when (= this# that#)
                           this#)
        (interval? that#) (intersection that# this#)
        :else (intersection* this# that#)))
     (~'difference [this# that#]
       (cond
        (integer? that#) (if (= this# that#)
                           nil
                           this#)
        (interval? that#) (difference that# this#)
        :else (difference* this# that#)))
     IIntervals
     (~'intervals [this#]
       (list this#))))

(extend-to-fd java.lang.Byte)
(extend-to-fd java.lang.Short)
(extend-to-fd java.lang.Integer)
(extend-to-fd java.lang.Long)
(extend-to-fd java.math.BigInteger)
(extend-to-fd clojure.lang.BigInt)

(declare interval)

;; IntervalFD
;; -----
;; Type optimized for interval arithmetic. Only stores bounds.
;;
;; _lb - lower bound
;; _ub - upper bound

(deftype IntervalFD [_lb _ub]
  Object
  (equals [_ o]
    (if (instance? IntervalFD o)
      (and (= _lb (lb o))
           (= _ub (ub o)))
      false))
  (toString [this]
    (pr-str this))
  IMemberCount
  (member-count [this] (inc (- _ub _lb)))
  IInterval
  (lb [_] _lb)
  (ub [_] _ub)
  ISortedDomain
  (drop-one [_]
    (let [nlb (inc _lb)]
      (when (<= nlb _ub)
        (interval nlb _ub))))
  (drop-before [this n]
    (cond
     (= n _ub) n
     (< n _lb) this
     (> n _ub) nil
     :else (interval n _ub)))
  (keep-before [this n]
    (cond
     (<= n _lb) nil
     (> n _ub) this
     :else (interval _lb (dec n))))
  IFiniteDomain
  (domain? [_] true)
  ISet
  (member? [this n]
    (and (>= n _lb) (<= n _ub)))
  (disjoint? [this that]
    (cond
     (integer? that)
     (not (member? this that))

     (interval? that)
     (let [i this
           j that
           [imin imax] (bounds i)
           [jmin jmax] (bounds j)]
       (or (> imin jmax)
           (< imax jmin)))

     :else (disjoint?* this that)))
  (intersection [this that]
    (cond
     (integer? that)
     (if (member? this that)
       that
       nil)

     (interval? that)
     (let [i this j that
           imin (lb i) imax (ub i)
           jmin (lb j) jmax (ub j)]
       (cond
        (< imax jmin) nil
        (< jmax imin) nil
        (and (<= imin jmin)
             (>= imax jmax)) j
        (and (<= jmin imin)
             (>= jmax imax)) i
        (and (<= imin jmin)
             (<= imax jmax)) (interval jmin imax)
        (and (<= jmin imin)
             (<= jmax imax)) (interval imin jmax)
        :else (throw (Error. (str "Interval intersection not defined " i " " j)))))

     :else (intersection* this that)))
  (difference [this that]
    (cond
     (integer? that)
     (cond
      (= _lb that) (interval (inc _lb) _ub)
      (= _ub that) (interval _lb (dec _ub))
      :else (if (member? this that)
              (multi-interval (interval _lb (dec that))
                              (interval (inc that) _ub))
              this))
     
     (interval? that)
     (let [i this j that
           imin (lb i) imax (ub i)
           jmin (lb j) jmax (ub j)]
       (cond
        (> jmin imax) i
        (and (<= jmin imin)
             (>= jmax imax)) nil
        (and (< imin jmin)
             (> imax jmax)) (multi-interval (interval imin (dec jmin))
             (interval (inc jmax) imax))
        (and (< imin jmin)
             (<= jmin imax)) (interval imin (dec jmin))
        (and (> imax jmax)
             (<= jmin imin)) (interval (inc jmax) imax)
        :else (throw (Error. (str "Interval difference not defined " i " " j)))))
     
     :else (difference* this that)))
  IIntervals
  (intervals [this]
    (list this)))

(defn interval? [x]
  (instance? IntervalFD x))

(defmethod print-method IntervalFD [x ^Writer writer]
  (.write writer (str "<interval:" (lb x) ".." (ub x) ">")))

(defn interval
  "Construct an interval for an assignment to a var. intervals may
   be more efficient that the domain type when the range of possiblities
   is large."
  ([ub] (IntervalFD. 0 ub))
  ([lb ub]
     (if (zero? (- ub lb))
       ub
       (IntervalFD. lb ub))))

(declare normalize-intervals singleton-dom? multi-interval)

;; MultiIntervalFD
;; -----
;; Running difference operations on IntervalFD will result in
;; a series of intervals.
;;
;; min - minimum value of all contained intervals
;; max - maximum value of all contained intervals
;; is  - the intervals

(deftype MultiIntervalFD [min max is]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :is is
      :min min
      :max max
      not-found))
  Object
  (equals [this j]
    (if (instance? MultiIntervalFD j)
      (let [i this
            [jmin jmax] (bounds j)]
        (if (and (= min jmin) (= max jmax))
          (let [is (normalize-intervals is)
                js (normalize-intervals (intervals j))]
            (= is js))
          false))
      false))
  IMemberCount
  (member-count [this]
    (reduce + 0 (map member-count is)))
  IInterval
  (lb [_] min)
  (ub [_] max)
  ISortedDomain
  (drop-one [_]
    (let [i (first is)]
      (if (singleton-dom? i)
        (let [nis (rest is)]
          (MultiIntervalFD. (lb (first nis)) max nis))
        (let [ni (drop-one i)]
          (MultiIntervalFD. (lb ni) max (cons ni (rest is)))))))
  (drop-before [_ n]
    (let [is (seq is)]
      (loop [is is r []]
        (if is
          (let [i (drop-before (first is) n)]
            (if i
              (recur (next is) (conj r i))
              (recur (next is) r)))
          (when (pos? (count r))
            (apply multi-interval r))))))
  (keep-before [_ n]
    (let [is (seq is)]
      (loop [is is r []]
        (if is
          (let [i (keep-before (first is) n)]
            (if i
              (recur (next is) (conj r i))
              (recur (next is) r)))
          (when (pos? (count r))
            (apply multi-interval r))))))
  IFiniteDomain
  (domain? [_] true)
  ISet
  (member? [this n]
    (if (some #(member? % n) is)
      true
      false))
  (disjoint? [this that]
    (disjoint?* this that))
  (intersection [this that]
    (intersection* this that))
  (difference [this that]
    (difference* this that))
  IIntervals
  (intervals [this]
    (seq is)))

(defn multi-interval
  ([] nil)
  ([i0] i0)
  ([i0 i1]
     (let [is [i0 i1]]
       (MultiIntervalFD. (reduce min (map lb is)) (reduce max (map ub is)) is)))
  ([i0 i1 & ir]
     (let [is (into [] (concat (list i0 i1) ir))]
       (MultiIntervalFD. (reduce min (map lb is)) (reduce max (map ub is)) is))))

(defmethod print-method MultiIntervalFD [x ^Writer writer]
  (.write writer (str "<intervals:" (apply pr-str (:is x)) ">")))

(deftype FDConstraint [proc _id _meta]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :proc proc
      not-found))
  Object
  (equals [this o]
    (if (instance? FDConstraint o)
      (and (= (rator this) (rator o))
           (= (rands this) (rands o)))
      false))
  clojure.lang.IObj
  (meta [this]
    _meta)
  (withMeta [this new-meta]
    (FDConstraint. proc _id new-meta))
  clojure.lang.IFn
  (invoke [_ s]
    (proc s))
  IEnforceableConstraint
  (enforceable? [_] true)
  IConstraintOp
  (rator [_] (rator proc))
  (rands [_] (rands proc))
  IRelevant
  (-relevant? [this s]
    (-relevant? proc s))
  IRunnable
  (runnable? [this s]
    (if (instance? clojure.core.logic.IRunnable proc)
      (runnable? proc s)
      (letfn [(has-dom? [x]
                (let [x (walk s x)]
                  (if (lvar? x)
                    (get-dom s x)
                    x)))]
        (every? identity (map has-dom? (rands proc))))))
  IWithConstraintId
  (with-id [this new-id] (FDConstraint. (with-id proc new-id) new-id _meta))
  IConstraintId
  (id [this] _id)
  IConstraintWatchedStores
  (watched-stores [this]
    (if (instance? clojure.core.logic.IConstraintWatchedStores proc)
      (watched-stores proc)
      #{::subst ::fd})))

(defn fdc [proc]
  (FDConstraint. proc nil nil))

(defmethod print-method FDConstraint [x ^Writer writer]
  (let [cid (if-let [cid (id x)]
             (str cid ":")
             "")]
    (.write writer (str "(" cid (rator (:proc x)) " " (apply str (interpose " " (rands (:proc x)))) ")"))))

(defn -domfdc [x]
  (reify
    clojure.lang.IFn
    (invoke [this s]
      (when (member? (get-dom s x) (walk s x))
        (rem-attr s x ::fd)))
    IConstraintOp
    (rator [_] `domfdc)
    (rands [_] [x])
    IRelevant
    (-relevant? [this s]
      (not (nil? (get-dom s x))))
    IRunnable
    (runnable? [this s]
      (not (lvar? (walk s x))))
    IConstraintWatchedStores
    (watched-stores [this] #{::subst})))

(defn domfdc [x]
  (cgoal (fdc (-domfdc x))))