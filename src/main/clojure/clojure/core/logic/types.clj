(ns clojure.core.logic.types
  (:use clojure.core.logic.protocols
        clojure.core.logic.protocols.clp
        clojure.core.logic.util
        clojure.core.logic.mk
        clojure.core.logic.clp
        clojure.core.logic.types.clp)
  (:import [java.io Writer]))

;; =============================================================================
;; Pair

(deftype Pair [lhs rhs]
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :lhs lhs
      :rhs rhs
      not-found))
  clojure.lang.Counted
  (count [_] 2)
  clojure.lang.Indexed
  (nth [_ i] (case i
                   0 lhs
                   1 rhs
                   (throw (IndexOutOfBoundsException.))))
  (nth [_ i not-found] (case i
                             0 lhs
                             1 rhs
                             not-found))
  java.util.Map$Entry
  (getKey [_] lhs)
  (getValue [_] rhs)
  Object
  (toString [_]
    (str "(" lhs " . " rhs ")"))
  (equals [_ o]
    (if (instance? Pair o)
      (and (= lhs (:lhs o))
           (= rhs (:rhs o)))
      false)))

(defn pair [lhs rhs]
  (Pair. lhs rhs))

(defmethod print-method Pair [x ^Writer writer]
  (.write writer (str "(" (:lhs x) " . " (:rhs x) ")")))

;; =============================================================================
;; SubstValue

(defrecord SubstValue [v]
  clojure.core.logic.protocols.ISubstValue
  Object
  (toString [_]
    (str v)))

(defn subst-val
  ([x] (SubstValue. x))
  ([x _meta] (with-meta (SubstValue. x) _meta)))

(defmethod print-method SubstValue [x ^Writer writer]
  (.write writer (str (:v x))))

;; Substitutions
;; -----
;; s   - persistent hashmap to store logic var bindings
;; l   - persistent list of var bindings to support disequality constraints
;; cs  - constraint store
;; cq  - for the constraint queue
;; cqs - constraint ids in the queue

(declare make-s empty-s)

(deftype Substitutions [s l cs cq cqs _meta]
  Object
  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (= s (:s o)))))
  ;; TODO: prn doesn't work anymore on empty-s, why not?
  (toString [_] (str s))

  clojure.lang.Counted
  (count [this] (count s))

  clojure.lang.IObj
  (meta [this] _meta)
  (withMeta [this new-meta]
    (Substitutions. s l cs cq cqs new-meta))

  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :s   s
      :l   l
      :cs  cs
      :cq  cq
      :cqs cqs
      not-found))

  clojure.lang.IPersistentCollection
  (cons [this [k v]]
    (if (lvar? k)
      (assoc this k v)
      (throw (Exception. (str "key must be a logic var")))))
  (empty [this] empty-s)
  (equiv [this o]
    (.equals this o))

  clojure.lang.Associative
  (containsKey [this k]
    (contains? #{:s :l :cs :cq :cqs} k))
  (entryAt [this k]
    (case k
      :s   [:s s]
      :l   [:l l]
      :cs  [:cs cs]
      :cq  [:cq cq]
      :cqs [:cqs cqs]
      nil))
  (assoc [this k v]
    (case k
      :s   (Substitutions. v l cs cq cqs _meta)
      :l   (Substitutions. s v cs cq cqs _meta)
      :cs  (Substitutions. s l  v cq cqs _meta)
      :cq  (Substitutions. s l cs  v cqs _meta)
      :cqs (Substitutions. s l cs cq v   _meta)
      (throw (Exception. (str "Substitutions has no field for key" k)))))

  ISubstitutions
  (-empty-s [_] (make-s))

  (ext-no-check [this u v]
    (let [u (assoc-meta u ::root true)
          l (if (and (subst-val? v)
                     (= (:v v) ::unbound))
              l
              (cons (pair u v) l))]
      (Substitutions. (assoc s u v) l cs cq cqs _meta)))

  (walk [this v]
    (if (lvar? v)
      (loop [lv v [v vp :as me] (find s v)]
        (cond
          (nil? me) lv
          
          (not (lvar? vp))
          (if-let [sv (and (subst-val? vp) (:v vp))]
            (if (= sv ::unbound)
              (with-meta v (assoc (meta vp) ::unbound true))
              sv)
            vp)
          
          :else (recur vp (find s vp))))
      v))

  ISubstitutionsCLP
  (root-val [this v]
    (if (lvar? v)
      (loop [lv v [v vp :as me] (find s v)]
        (cond
          (nil? me) lv
          (not (lvar? vp)) vp
          :else (recur vp (find s vp))))
      v))

  (root-var [this v]
    (if (lvar? v)
      (if (-> v meta ::root)
        v
        (loop [lv v [v vp :as me] (find s v)]
          (cond
            (nil? me) lv

            (not (lvar? vp))
            (if (subst-val? vp)
              (with-meta v (meta vp))
              v)

            :else (recur vp (find s vp)))))
      v))
  
  (update [this x v]
    (let [xv (root-val this x)
          sval? (subst-val? xv)]
      (if (or (lvar? xv) (and sval? (= (:v xv) ::unbound)))
        (let [x  (root-var this x)
              xs (if (lvar? v)
                   [x (root-var this v)]
                   [x])]
          ((run-constraints* xs cs ::subst)
           (let [v (if sval? (assoc xv :v v) v)]
             (if *occurs-check*
               (ext this x v)
               (ext-no-check this x v)))))
        (when (= (if sval? (:v xv) v) v) ;; NOTE: replace with unify?
          this))))

  (queue [this c]
    (let [id (id c)]
      (if-not (cqs id)
        (-> this
          (assoc :cq (conj (or cq []) c))
          (assoc :cqs (conj cqs id)))
        this)))

  (update-var [this x v]
    (assoc this :s (assoc (:s this) x v)))

  (add-attr [this x attr attrv]
    (let [x (root-var this x)
          v (root-val this x)]
      (if (subst-val? v)
        (update-var this x (assoc-meta v attr attrv))
        (let [v (if (lvar? v) ::unbound v)]
          (ext-no-check this x (subst-val v {attr attrv}))))))

  (rem-attr [this x attr]
    (let [x (root-var this x)
          v (root-val this x)]
      (if (subst-val? v)
        (let [new-meta (dissoc (meta v) attr)]
          (if (and (zero? (count new-meta)) (not= (:v v) ::unbound))
            (update-var this x (:v v))
            (update-var this x (with-meta v new-meta))))
        this)))

  (get-attr [this x attr]
    (let [v (root-val this x)]
      (if (subst-val? v)
        (-> v meta attr))))

  IBind
  (bind [this g]
    (g this))
  IMPlus
  (mplus [this f]
    (choice this f))
  ITake
  (take* [this] this))

(defn- make-s
  ([] (Substitutions. {} () (make-cs) nil #{} nil))
  ([m] (Substitutions. m () (make-cs) nil #{} nil))
  ([m l] (Substitutions. m l (make-cs) nil #{} nil))
  ([m l cs] (Substitutions. m l cs nil #{} nil)))

(def empty-s (make-s))
(def empty-f (fn []))

(defn subst? [x]
  (instance? Substitutions x))

(defn to-s [v]
  (let [s (reduce (fn [m [k v]] (assoc m k v)) {} v)
        l (reduce (fn [l [k v]] (cons (Pair. k v) l)) '() v)]
    (make-s s l (make-cs))))

(defn annotate [k v]
  (fn [a]
    (vary-meta a assoc k v)))

;; =============================================================================
;; Logic Variables

(deftype LVar [name oname hash meta]
  clojure.core.logic.protocols.IVar
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [this k not-found]
    (case k
      :name name
      :oname oname
      not-found))
  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LVar. name oname hash new-meta))
  Object
  (toString [_] (str "<lvar:" name ">"))
  (equals [this o]
    (and (lvar? o)
      (identical? name (:name o))))
  (hashCode [_] hash)
  IUnifyTerms
  (unify-terms [u v s]
    (unify-with-lvar v u s))
  IUnifyWithNil
  (unify-with-nil [v u s]
    (ext-no-check s v u))
  IUnifyWithObject
  (unify-with-object [v u s]
    (if (= u ::not-found)
      nil
      (ext s v u)))
  IUnifyWithLVar
  (unify-with-lvar [v u s]
    (if (-> u clojure.core/meta ::unbound)
      (let [s (if (-> v clojure.core/meta ::unbound)
                (assoc s :cs (migrate (:cs s) v u))
                s)]
        (ext-no-check s v u))
      (ext-no-check s u v)))
  IUnifyWithLSeq
  (unify-with-lseq [v u s]
    (ext s v u))
  IUnifyWithSequential
  (unify-with-seq [v u s]
    (ext s v u))
  IUnifyWithMap
  (unify-with-map [v u s]
    (ext s v u))
  IReifyTerm
  (reify-term [v s]
    (if *reify-vars*
      (ext s v (reify-lvar-name s))
      (ext s v (:oname v))))
  IWalkTerm
  (walk-term [v f] (f v))
  IOccursCheckTerm
  (occurs-check-term [v x s] (= (walk s v) x)))

(defn lvar
  ([]
     (let [name (str (. clojure.lang.RT (nextID)))]
       (LVar. name nil (.hashCode name) nil)))
  ([name]
     (let [oname name
           name (str name "_" (. clojure.lang.RT (nextID)))]
       (LVar. name oname (.hashCode name) nil))))

(defmethod print-method LVar [x ^Writer writer]
  (.write writer (str "<lvar:" (:name x) ">")))

;; =============================================================================
;; LCons

(defmacro umi
  [& args]
  (if (resolve 'unchecked-multiply-int)
    `(unchecked-multiply-int ~@args)
    `(unchecked-multiply ~@args)))

(defmacro uai
  [& args]
  (if (resolve 'unchecked-add-int)
    `(unchecked-add-int ~@args)
    `(unchecked-add ~@args)))

(declare lcons)

;; TODO: clean up the printing code

(deftype LCons [a d ^{:unsynchronized-mutable true :tag int} cache meta]
  clojure.core.logic.protocols.ILCons
  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LCons. a d cache new-meta))
  LConsSeq
  (lfirst [_] a)
  (lnext [_] d)
  LConsPrint
  (toShortString [this]
    (cond
     (.. this getClass (isInstance d)) (str a " " (toShortString d))
     :else (str a " . " d )))
  Object
  (toString [this] (cond
                    (.. this getClass (isInstance d))
                      (str "(" a " " (toShortString d) ")")
                    :else (str "(" a " . " d ")")))
  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (loop [me this
                    you o]
               (cond
                (nil? me) (nil? you)
                (lvar? me) true
                (lvar? you) true
                (and (lcons? me) (lcons? you))
                  (let [mef  (lfirst me)
                        youf (lfirst you)]
                    (and (or (= mef youf)
                             (lvar? mef)
                             (lvar? youf))
                         (recur (lnext me) (lnext you))))
                :else (= me you))))))

  (hashCode [this]
    (if (= cache -1)
      (do
        (set! cache (uai (umi (int 31) (clojure.lang.Util/hash d))
                         (clojure.lang.Util/hash a)))
        cache)
      cache))
  IUnifyTerms
  (unify-terms [u v s]
    (unify-with-lseq v u s))
  IUnifyWithNil
  (unify-with-nil [v u s] nil)
  IUnifyWithObject
  (unify-with-object [v u s] nil)
  IUnifyWithLSeq
  (unify-with-lseq [v u s]
    (loop [u u v v s s]
      (if (lvar? u)
        (unify s u v)
        (cond
         (lvar? v) (unify s v u)
         (and (lcons? u) (lcons? v))
           (if-let [s (unify s (lfirst u) (lfirst v))]
             (recur (lnext u) (lnext v) s)
             nil)
         :else (unify s u v)))))
  IUnifyWithSequential
  (unify-with-seq [v u s]
    (unify-with-lseq u v s))
  IUnifyWithMap
  (unify-with-map [v u s] nil)
  IReifyTerm
  (reify-term [v s]
    (loop [v v s s]
      (if (lcons? v)
        (recur (lnext v) (-reify* s (lfirst v)))
        (-reify* s v))))
  ;; TODO: no way to make this non-stack consuming w/o a lot more thinking
  ;; we could use continuation passing style and trampoline
  IWalkTerm
  (walk-term [v f]
    (lcons (f (lfirst v))
           (f (lnext v))))
  IOccursCheckTerm
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (lcons? v)
        (or (occurs-check s x (lfirst v))
            (recur (lnext v) x s))
        (occurs-check s x v)))))

(defmethod print-method LCons [x ^Writer writer]
  (.write writer (str x)))

(defn lcons
  "Constructs a sequence a with an improper tail d if d is a logic variable."
  [a d]
  (if (or (coll? d) (nil? d))
    (cons a (seq d))
    (LCons. a d -1 nil)))

(defmacro llist
  "Constructs a sequence from 2 or more arguments, with the last argument as the
   tail. The tail is improper if the last argument is a logic variable."
  ([f s] `(lcons ~f ~s))
  ([f s & rest] `(lcons ~f (llist ~s ~@rest))))
