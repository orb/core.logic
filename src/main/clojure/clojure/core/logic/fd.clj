(ns clojure.core.logic.fd
  (:refer-clojure :exclude [+ - * = quot < > <= >=])
  (:require [clojure.core :as core])
  (:use clojure.core.logic.types
        clojure.core.logic.protocols.fd))

(defn bounds [i]
  (pair (lb i) (ub i)))

(defn interval-< [i j]
  (core/< (ub i) (lb j)))

(defn interval-> [i j]
  (core/> (lb i) (ub j)))

(defn intersection* [is js]
  (loop [is (seq (intervals is)) js (seq (intervals js)) r []]
    (if (and is js)
      (let [i (first is)
            j (first js)]
        (cond
         (interval-< i j) (recur (next is) js r)
         (interval-> i j) (recur is (next js) r)
         :else
         (let [[imin imax] (bounds i)
               [jmin jmax] (bounds j)]
           (cond
            (core/<= imin jmin)
            (cond
             (core/< imax jmax)
             (recur (next is)
                    (cons (interval (inc imax) jmax) (next js))
                    (conj r (interval jmin imax)))
             (core/> imax jmax)
             (recur (cons (interval (inc jmax) imax) (next is))
                    (next js)
                    (conj r j))
             :else
             (recur (next is) (next js)
                    (conj r (interval jmin jmax))))
            (core/> imin jmin)
            (cond
             (core/> imax jmax)
             (recur (cons (interval (inc jmax) imax) (next is))
                    (next js)
                    (conj r (interval imin jmax)))
             (core/< imax jmax)
             (recur is (cons (interval (inc imax) jmax) (next js))
                    (conj r i))
             :else
             (recur (next is) (next js)
                    (conj r (interval imin imax))))))))
      (apply multi-interval r))))

(defn difference* [is js]
    (loop [is (seq (intervals is)) js (seq (intervals js)) r []]
      (if is
        (if js
          (let [i (first is)
                j (first js)]
            (cond
             (interval-< i j) (recur (next is) js (conj r i))
             (interval-> i j) (recur is (next js) r)
             :else
             (let [[imin imax] (bounds i)
                   [jmin jmax] (bounds j)]
               (cond
                (core/< imin jmin)
                (cond
                 (core/< jmax imax)
                 (recur (cons (interval (inc jmax) imax) (next is))
                        (next js)
                        (conj r (interval imin (dec jmin))))
                 (core/> jmax imax)
                 (recur (next is)
                        (cons (interval (inc imax) jmax) (next js))
                        (conj r (interval imin (dec jmin))))
                 :else
                 (recur (next is) (next js)
                        (conj r (interval imin (dec jmin)))))
                (core/>= imin jmin)
                (cond
                 (core/< imax jmax)
                 (recur (next is)
                        (cons (interval (inc imax) jmax) (next js))
                        r)
                 (core/> imax jmax)
                 (recur (cons (interval (inc jmax) imax) (next is))
                        (next js)
                        r)
                 :else (recur (next is) (next js)
                              r))))))
          (apply multi-interval (into r is)))
        (apply multi-interval r))))

(defn disjoint?* [is js]
  (if (disjoint? (interval (lb is) (ub is))
                 (interval (lb js) (ub js)))
      true
      (let [d0 (intervals is)
            d1 (intervals js)]
        (loop [d0 d0 d1 d1]
          (if (nil? d0)
            true
            (let [i (first d0)
                  j (first d1)]
              (cond
               (or (interval-< i j) (disjoint? i j)) (recur (next d0) d1)
               (interval-> i j) (recur d0 (next d1))
               :else false)))))))

;; union where possible
(defn normalize-intervals [is]
  (reduce (fn [r i]
            (if (zero? (count r))
              (conj r i)
              (let [j (peek r)
                    jmax (ub j)
                    imin (lb i)]
                (if (<= (dec imin) jmax)
                  (conj (pop r) (interval (lb j) (ub i)))
                  (conj r i)))))
    [] is))

;; =============================================================================
;; cKanren

;; See - Claire Alvis, Dan Friedman, Will Byrd, et al
;; "cKanren - miniKanren with Constraints"
;; http://www.schemeworkshop.org/2011/papers/Alvis2011.pdf
;; http://github.com/calvis/cKanren

(defn get-dom
  [a x]
  (if (lvar? x)
    (get-attr a x ::fd)
    x))

(defn ext-dom
  [a x dom]
  (let [x    (root-var a x)
        domp (get-dom a x)
        a    (add-attr a x ::fd dom)]
    (if (not= domp dom)
      ((run-constraints* [x] (:cs a) ::fd) a)
      a)))

(declare get-dom)

(defn singleton-dom? [x]
  (integer? x))

(defmacro let-dom
  [a vars & body]
  (let [get-var-dom (fn [a [v b]]
                      `(~b (let [v# (walk ~a ~v)]
                             (if (lvar? v#)
                               (get-dom ~a v#)
                               v#))))]
   `(let [~@(mapcat (partial get-var-dom a) (partition 2 vars))]
      ~@body)))

(defn resolve-storable-dom
  [a x dom]
  (if (singleton-dom? dom)
    (update (rem-attr a x ::fd) x dom)
    (ext-dom a x dom)))

(defn update-var-dom
  [a x dom]
  (let [domp (get-dom a x)]
    (if domp
      (let [i (intersection dom domp)]
        (when i
          (resolve-storable-dom a x i)))
      (resolve-storable-dom a x dom))))

(defn process-dom
  "If x is a var we update its domain. If it's an integer
   we check that it's a member of the given domain."
  [x dom]
  (fn [a]
    (when dom
      (cond
       (lvar? x) (update-var-dom a x dom)
       (member? dom x) a
       :else nil))))

(declare domfdc)

(defn sort-by-member-count [a]
  (fn [x y]
    (let-dom a [x dx y dy]
      (< (member-count dx) (member-count dy)))))

;; TODO: handle all Clojure tree types

(defn =c [u v]
  (reify
    clojure.lang.IFn
    (invoke [this s]
      (let-dom s [u du v dv]
        (let [i (intersection du dv)]
          ((composeg
            (process-dom u i)
            (process-dom v i)) s))))
    IConstraintOp
    (rator [_] `=)
    (rands [_] [u v])
    IRelevant
    (-relevant? [this s]
      (let-dom s [u du v dv]
        (cond
         (not (singleton-dom? du)) true
         (not (singleton-dom? dv)) true
         :else (not= du dv))))))

(defn =
  "A finite domain constraint. u and v must be equal. u and v must
   eventually be given domains if vars."
  [u v]
  (cgoal (fdc (=c u v))))

(defn !=c [u v]
  (reify 
    clojure.lang.IFn
    (invoke [this s]
      (let-dom s [u du v dv]
        (cond
         (and (singleton-dom? du)
              (singleton-dom? dv)
              (core/= du dv)) nil
         (disjoint? du dv) s
         (singleton-dom? du)
         (when-let [vdiff (difference dv du)]
           ((process-dom v vdiff) s))
         :else (when-let [udiff (difference du dv)]
                 ((process-dom u udiff) s)))))
    IConstraintOp
    (rator [_] `!=)
    (rands [_] [u v])
    IRelevant
    (-relevant? [this s]
      (let-dom s [u du v dv]
        (not (and (domain? du) (domain? dv) (disjoint? du dv)))))
    IRunnable
    (runnable? [this s]
      (let-dom s [u du v dv]
        ;; we are runnable if du and dv both have domains
        ;; and at least du or dv has a singleton domain
        (and (domain? du) (domain? dv)
             (or (singleton-dom? du)
                 (singleton-dom? dv))))))) 

(defn !=
  "A finite domain constraint. u and v must not be equal. u and v
   must eventually be given domains if vars."
  [u v]
  (cgoal (fdc (!=c u v))))

(defn <=c [u v]
  (reify 
    clojure.lang.IFn
    (invoke [this s]
      (let-dom s [u du v dv]
        (let [umin (lb du)
              vmax (ub dv)]
         ((composeg*
           (process-dom u (keep-before du (inc vmax)))
           (process-dom v (drop-before dv umin))) s))))
    IConstraintOp
    (rator [_] `<=)
    (rands [_] [u v])
    IRelevant
    (-relevant? [this s]
      (let-dom s [u du v dv]
       (cond
        (not (singleton-dom? du)) true
        (not (singleton-dom? dv)) true
        :else (not (<= du dv)))))))

(defn <=
  "A finite domain constraint. u must be less than or equal to v.
   u and v must eventually be given domains if vars."
  [u v]
  (cgoal (fdc (<=c u v))))

(defn <
  "A finite domain constraint. u must be less than v. u and v
   must eventually be given domains if vars."
  [u v]
  (all
   (<= u v)
   (!= u v)))

(defn >
  "A finite domain constraint. u must be greater than v. u and v
   must eventually be given domains if vars."
  [u v]
  (< v u))

(defn >=
  "A finite domain constraint. u must be greater than or equal to v.
   u and v must eventually be given domains if vars."
  [u v]
  (<= v u))

;; NOTE: we could put logic right back in but then we're managing
;; the constraint in the body again which were trying to get
;; away from

(defn +fdc-guard [u v w]
  (fn [s]
    (let-dom s [u du v dv w dw]
      (if (every? singleton-dom? [du dv dw])
        (when (core/= (core/+ du dv) dw)
          s)
        s))))

(defn +c [u v w]
  (reify 
    clojure.lang.IFn
    (invoke [this s]
      (let-dom s [u du v dv w dw]
        (let [[wmin wmax] (if (domain? dw)
                            (bounds dw)
                            [(core/+ (lb du) (lb dv)) (core/+ (ub du) (ub dv))])
              [umin umax] (if (domain? du)
                            (bounds du)
                            [(core/- (lb dw) (ub dv)) (core/- (ub dw) (lb dv))])
              [vmin vmax] (if (domain? dv)
                            (bounds dv)
                            [(core/- (lb dw) (ub du)) (core/- (ub dw) (lb du))])]
          ((composeg*
            (process-dom w (interval (core/+ umin vmin) (core/+ umax vmax)))
            (processcore/-dom u (interval (core/- wmin vmax) (core/- wmax vmin)))
            (processcore/-dom v (interval (core/- wmin umax) (core/- wmax umin)))
            (+fdc-guard u v w))
           s))))
    IConstraintOp
    (rator [_] `+)
    (rands [_] [u v w])
    IRelevant
    (-relevant? [this s]
      (let-dom s [u du v dv w dw]
        (cond
         (not (singleton-dom? du)) true
         (not (singleton-dom? dv)) true
         (not (singleton-dom? dw)) true
         :else (not= (core/+ du dv) dw))))
    IRunnable
    (runnable? [this s]
      ;; we want to run even if w doesn't have a domain
      ;; this is to support eqfd
      (let-dom s [u du v dv w dw]
        (cond
          (domain? du) (or (domain? dv) (domain? dw))
          (domain? dv) (or (domain? du) (domain? dw))
          (domain? dw) (or (domain? du) (domain? dv))
          :else false)))))

(defn +
  "A finite domain constraint for addition and subtraction.
   u, v & w must eventually be given domains if vars."
  [u v w]
  (cgoal (fdc (+c u v w))))

(defn -
  [u v w]
  (+ v w u))

;; TODO NOW: we run into trouble with division this is why
;; simplefd in bench.clj needs map-sum when it should not

(defn *c-guard [u v w]
  (fn [s]
    (let-dom s [u du v dv w dw]
      (if (every? singleton-dom? [du dv dw])
        (when (core/= (core/* du dv) dw)
          s)
        s))))

(defn *c [u v w]
  (letfn [(safe-div [n c a t]
            (if (zero? n)
              c
              (let [q (core/quot a n)]
                (case t
                  :lower (if (pos? (rem a n))
                           (inc q)
                           q)
                  :upper q))))]
   (reify
     clojure.lang.IFn
     (invoke [this s]
       (let-dom s [u du v dv w dw]
         (let [[wmin wmax] (if (domain? dw)
                             (bounds dw)
                             [(core/* (lb du) (lb dv)) (core/* (ub du) (ub dv))])
               [umin umax] (if (domain? du)
                             (bounds du)
                             [(safe-div (ub dv) (lb dw) (lb dw) :lower)
                              (safe-div (lb dv) (lb dw) (ub dw) :upper)])
               [vmin vmax] (if (domain? dv)
                             (bounds dv)
                             [(safe-div (ub du) (lb dw) (lb dw) :lower)
                              (safe-div (lb du) (lb dw) (ub dw) :upper)])
               wi (interval (core/* umin vmin) (core/* umax vmax))
               ui (interval (safe-div vmax umin wmin :lower)
                            (safe-div vmin umax wmax :upper))
               vi (interval (safe-div umax vmin wmin :lower)
                            (safe-div umin vmax wmax :upper))]
           ((composeg*
             (process-dom w wi)
             (process-dom u ui)
             (process-dom v vi)
             (*c-guard u v w)) s))))
     IConstraintOp
     (rator [_] `*)
     (rands [_] [u v w])
     IRelevant
     (-relevant? [this s]
       (let-dom s [u du v dv w dw]
         (cond
          (not (singleton-dom? du)) true
          (not (singleton-dom? dv)) true
          (not (singleton-dom? dw)) true
          :else (not= (core/* du dv) dw))))
     IRunnable
     (runnable? [this s]
       ;; we want to run even if w doesn't have a domain
       ;; this is to support eqfd
       (let-dom s [u du v dv w dw]
         (cond
          (domain? du) (or (domain? dv) (domain? dw))
          (domain? dv) (or (domain? du) (domain? dw))
          (domain? dw) (or (domain? du) (domain? dv))
          :else false))))))

(defn *
  "A finite domain constraint for multiplication and
   thus division. u, v & w must be eventually be given 
   domains if vars."
  [u v w]
  (cgoal (fdc (*c u v w))))

(defn quot [u v w]
  (* v w u))

(defn -distinctfdc
  "The real *individual* distinctfd constraint. x is a var that now is bound to
   a single value. y* were the non-singleton bound vars that existed at the
   construction of the constraint. n* is the set of singleton domain values 
   that existed at the construction of the constraint. We use categorize to 
   determine the current non-singleton bound vars and singleton vlaues. if x
   is in n* or the new singletons we have failed. If not we simply remove 
   the value of x from the remaining non-singleton domains bound to vars."
  ([x y* n*] (-distinctfdc x y* n* nil))
  ([x y* n* id]
     (reify
       clojure.lang.IFn
       (invoke [this s]
         (let [x (walk s x)]
           (when-not (n* x)
             (loop [y* (seq y*) s s]
               (if y*
                 (let [y (first y*)
                       v (or (get-dom s y) (walk s y))
                       s (if-not (lvar? v)
                           (cond
                             (core/= x v) nil
                             (member? v x) ((process-dom y (difference v x)) s)
                             :else s)
                           s)]
                   (when s
                     (recur (next y*) s)))
                 ((remcg this) s))))))
       IWithConstraintId
       (with-id [this id]
         (-distinctfdc x y* n* id))
       IConstraintId
       (id [this] id)
       IConstraintOp
       (rator [_] `-distinctfd)
       (rands [_] [x])
       IRelevant
       (-relevant? [this s] true) ;; we are relevant until we run
       IRunnable
       (runnable? [this s]
         ;; we can only run if x is is bound to
         ;; a single value
         (singleton-dom? (walk s x)))
       IConstraintWatchedStores
       (watched-stores [this] #{::subst}))))

(defn -distinctc [x y* n*]
  (cgoal (fdc (-distinctc x y* n*))))

(defn list-sorted? [pred ls]
  (if (empty? ls)
    true
    (loop [f (first ls) ls (next ls)]
      (if ls
        (let [s (first ls)]
         (if (pred f s)
           (recur s (next ls))
           false))
        true))))

(defn distinctc
  "The real distinctfd constraint. v* can be seq of logic vars and
   values or it can be a logic var itself. This constraint does not 
   run until v* has become ground. When it has become ground we group
   v* into a set of logic vars and a sorted set of known singleton 
   values. We then construct the individual constraint for each var."
  ([v*] (distinctc v* nil))
  ([v* id]
     (reify
       clojure.lang.IFn
       (invoke [this s]
         (let [v* (walk s v*)
               {x* true n* false} (group-by lvar? v*)
               n* (sort core/< n*)]
           (when (list-sorted? < n*)
             (let [x* (into #{} x*)
                   n* (into (sorted-set) n*)]
               (loop [xs (seq x*) s s]
                 (if xs
                   (let [x (first xs)]
                     (when-let [s ((-distinctfd x (disj x* x) n*) s)]
                       (recur (next xs) s)))
                   ((remcg this) s)))))))
       IWithConstraintId
       (with-id [this id]
         (distinctc v* id))
       IConstraintId
       (id [this] id)
       IConstraintOp
       (rator [_] `distinctfd)
       (rands [_] [v*])
       IRelevant
       (-relevant? [this s]
         true)
       IRunnable
       (runnable? [this s]
         (let [v* (walk s v*)]
           (not (lvar? v*))))
       IConstraintWatchedStores
       (watched-stores [this] #{::subst}))))

(defn distinct
  "A finite domain constraint that will guarantee that 
   all vars that occur in v* will be unified with unique 
   values. v* need not be ground. Any vars in v* should
   eventually be given a domain."
  [v*]
  (cgoal (fdc (distinctc v*))))

(defn distribute [v* strategy]
  (fn [a]
    (add-attr a v* ::strategy ::ff)))

;; -----------------------------------------------------------------------------
;; FD Equation Sugar

(def binops->fd
  '{+  clojure.core.logic/+fd
    -  clojure.core.logic/-fd
    *  clojure.core.logic/*fd
    /  clojure.core.logic/quotfd
    =  clojure.core.logic/==
    != clojure.core.logic/!=fd
    <= clojure.core.logic/<=fd
    <  clojure.core.logic/<fd
    >= clojure.core.logic/>=fd
    >  clojure.core.logic/>fd})

(def binops (set (keys binops->fd)))

(defn expand [form]
  (if (seq? form)
    (let [[op & args] form]
     (if (and (binops op) (core/> (count args) 2))
       (list op (expand (first args))
             (expand (cons op (rest args))))
       (cons op (map expand args))))
    form))

(defn eqfd*
  ([form vars] (eqfd* form vars nil))
  ([form vars out]
     (if (seq? form)
       (let [[op r1 r2] form
             [outl outlv?] (if (seq? r1)
                             (let [s (gensym)]
                               (swap! vars conj s)
                               [s true])
                             [r1 false])
             [outr outrv?] (if (seq? r2)
                             (let [s (gensym)]
                               (swap! vars conj s)
                               [s true])
                             [r2 false])
             op (binops->fd op)]
         (cons (if out
                 (list op outl outr out)
                 (list op outl outr))
               (concat (when (seq? r1)
                         (eqfd* r1 vars (when outlv? outl)))
                       (when (seq? r2)
                         (eqfd* r2 vars (when outrv? outr))))))
       form)))

(defn ->fd [vars exprs]
  `(fresh [~@vars]
     ~@(reverse exprs)))

(defn eqfd-form [form]
  (let [vars (atom [])
        exprs (eqfd* (expand form) vars)]
    (->fd @vars exprs)))

(defmacro eq [& forms]
  `(all
    ~@(map eqfd-form forms)))

(defn dom
  "Assign a var x a domain."
  [x dom]
  (fn [a]
    ((composeg
      (process-dom x dom)
      (if (nil? (get-dom a x))
        (domfdc x)
        identity)) a)))

(defmacro in
  "Assign vars to domain. The domain must come last."
  [& xs-and-dom]
  (let [xs (butlast xs-and-dom)
        dom (last xs-and-dom)
        domsym (gensym "dom_")]
    `(let [~domsym ~dom]
      (fresh []
        ~@(map (fn [x]
                 `(domfd ~x ~domsym))
               xs)))))

(defn to-vals [dom]
  (letfn [(to-vals* [is]
            (when is
              (let [i (first is)]
                (lazy-seq
                 (cons (lb i)
                       (if-let [ni (drop-one i)]
                         (to-vals* (cons ni (next is)))
                         (to-vals* (next is))))))))]
    (to-vals* (seq (intervals dom)))))