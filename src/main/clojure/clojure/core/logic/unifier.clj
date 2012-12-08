(ns clojure.core.logic.unifier)

(defmulti prep-subst (fn [lvar-expr] (::ann (meta lvar-expr))))

(defmethod prep-subst :default
  [lvar-expr] (lvar lvar-expr))

(defn- lvarq-sym? [s]
  (and (symbol? s) (= (first (str s)) \?)))

(defn- proc-lvar [lvar-expr store]
  (let [v (if-let [u (@store lvar-expr)]
            u
            (prep-subst lvar-expr))]
    (swap! store conj [lvar-expr v])
    v))

(defn- lcons-expr? [expr]
  (and (seq? expr) (some '#{.} (set expr))))

(declare prep*)

(defn- replace-lvar [store]
  (fn [expr]
    (if (lvarq-sym? expr)
      (proc-lvar expr store)
      (if (lcons-expr? expr)
        (prep* expr store)
        expr))))

(defn- prep*
  ([expr store] (prep* expr store false false))
  ([expr store lcons?] (prep* expr store lcons? false))
  ([expr store lcons? last?]
     (let [expr (if (and last? (seq expr))
                  (first expr)
                  expr)]
       (cond
        (lvarq-sym? expr) (proc-lvar expr store)
        (seq? expr) (if (or lcons? (lcons-expr? expr))
                      (let [[f & n] expr
                            skip (= f '.)
                            tail (prep* n store lcons? skip)]
                        (if skip
                          tail
                          (lcons (prep* f store) tail)))
                      (doall (walk-term expr (replace-lvar store))))
        :else expr))))

(defn prep
  "Prep a quoted expression. All symbols preceded by ? will
  be replaced with logic vars."
  [expr]
  (let [lvars (atom {})
        prepped (if (lcons-expr? expr)
                  (prep* expr lvars true)
                  (doall (walk-term expr (replace-lvar lvars))))]
    (with-meta prepped {:lvars @lvars})))

(declare fix-constraints)

(defn unifier*
  "Unify the terms u and w."
  ([u w]
     (first
      (run* [q]
        (== u w)
        (== q u)
        (fn [a]
          (fix-constraints a)))))
  ([u w & ts]
     (apply unifier* (unifier* u w) ts)))

(defn binding-map*
  "Return the binding map that unifies terms u and w.
  u and w should prepped terms."
  ([u w]
     (let [lvars (merge (-> u meta :lvars)
                        (-> w meta :lvars))
           s (unify empty-s u w)]
       (when s
         (into {} (map (fn [[k v]]
                         [k (-reify s v)])
                       lvars)))))
  ([u w & ts]
     (apply binding-map* (binding-map* u w) ts)))

(defn unifier
  "Unify the terms u and w. Will prep the terms."
  ([u w]
     {:pre [(not (lcons? u))
            (not (lcons? w))]}
     (let [up (prep u)
           wp (prep w)]
       (unifier* up wp)))
  ([u w & ts]
     (apply unifier (unifier u w) ts)))

(defn binding-map
  "Return the binding map that unifies terms u and w.
  Will prep the terms."
  ([u w]
     {:pre [(not (lcons? u))
            (not (lcons? w))]}
     (let [up (prep u)
           wp (prep w)]
       (binding-map* up wp)))
  ([u w & ts]
     (apply binding-map (binding-map u w) ts)))

(defprotocol IUnifyWithCVar
  (unify-with-cvar [v u s]))

(extend-protocol IUnifyWithCVar
  nil
  (unify-with-cvar [v u s]
    (queue (unify v (:lvar u)) (:c u)))

  Object
  (unify-with-cvar [v u s]
    (queue (unify s v (:lvar u)) (:c u)))

  LVar
  (unify-with-cvar [v u s]
    (-> (unify s v (:lvar u))
        (queue (:c u)))))

(declare cvar)

(deftype CVar [lvar c]
  clojure.core.logic.protocols.IVar
  Object
  (toString [_]
    (str lvar " :- " c))
  (hashCode [_]
    (.hashCode lvar))
  (equals [this o]
    (and (lvar? o)
      (identical? (:name lvar) (:name o))))
  clojure.lang.IObj
  (withMeta [this new-meta]
    (cvar (with-meta lvar new-meta) c))
  (meta [this]
    (meta lvar))
  clojure.lang.ILookup
  (valAt [this k]
    (.valAt this k nil))
  (valAt [_ k not-found]
    (case k
      :lvar lvar
      :name (:name lvar)
      :c c
      not-found))
  IUnifyTerms
  (unify-terms [u v s]
    (unify-with-cvar v u s))
  IUnifyWithObject
  (unify-with-object [v u s]
    (-> (unify s (:lvar v) u)
        (queue (:c v))))
  IUnifyWithLVar
  (unify-with-lvar [v u s]
    (-> (unify s (:lvar v) u)
        (queue (:c v))))
  IUnifyWithCVar
  (unify-with-cvar [v u s]
    (-> (unify s (:lvar v) (:lvar u))
        (queue (:c u))
        (queue (:c v)))))

(defn cvar [lvar c]
  (CVar. lvar c))

;; =============================================================================
;; GhostVal

;; for ghost val we need to be able to add goals?
;; gvar? logic vars that queue goals - to implement or functionality

;; =============================================================================
;; Some default prep substitutions

(defmethod prep-subst ::numeric
  [x] (let [x (lvar x)]
        (cvar x (-predc x number? `number?))))