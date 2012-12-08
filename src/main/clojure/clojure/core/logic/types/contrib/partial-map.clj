(ns clojure.core.logic.contrib.partial-map
  (:import [java.io Writer]))

(defn walk-record-term [v f]
  (with-meta
    (loop [v v r (-uninitialized v)]
      (if (seq v)
        (let [[vfk vfv] (first v)]
          (recur (next v) (assoc r (walk-term (f vfk) f)
                                 (walk-term (f vfv) f))))
        r))
    (meta v)))

(defprotocol IUnifyWithPMap
  (unify-with-pmap [pmap u s]))

(defn unify-with-pmap* [u v s]
  (loop [ks (keys u) s s]
    (if (seq ks)
      (let [kf (first ks)
            vf (get v kf ::not-found)
            uf (get u kf)]
        (if (= vf ::not-found)
          (if (= uf ::not-found)
            (recur (next ks) s)
            nil)
          (if (= uf ::not-found)
            nil
            (if-let [s (unify s uf vf)]
              (recur (next ks) s)
              nil))))
      s)))

(defrecord PMap []
  IUnifyWithMap
  (unify-with-map [v u s]
    (unify-with-pmap* v u s))

  IUnifyWithPMap
  (unify-with-pmap [v u s]
    (unify-with-pmap* v u s))

  IUnifyTerms
  (unify-terms [u v s]
    (unify-with-pmap v u s))

  IUnifyWithLVar
  (unify-with-lvar [v u s]
    (ext-no-check s u v))

  IUninitialized
  (-uninitialized [_] (PMap.))

  IWalkTerm
  (walk-term [v f]
    (walk-record-term v f)))

(extend-protocol IUnifyWithPMap
  nil
  (unify-with-pmap [v u s] nil)

  Object
  (unify-with-pmap [v u s] nil)

  clojure.core.logic.LVar
  (unify-with-pmap [v u s]
    (ext s v u))

  clojure.lang.IPersistentMap
  (unify-with-pmap [v u s]
    (unify-with-pmap* u v s)))

(defn partial-map
  "Given map m, returns partial map that unifies with maps even if it
   doesn't share all of the keys of that map.
   Only the keys of the partial map will be unified:

   (run* [q]
     (fresh [pm x]
       (== pm (partial-map {:a x}))
       (== pm {:a 1 :b 2})
       (== pm q)))
   ;;=> ({:a 1})"
  [m]
  (map->PMap m))