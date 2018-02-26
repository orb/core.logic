(defproject org.clojars.normanrichards/core.logic "0.8.11-1"
  :description "A logic/relational programming library for Clojure"
  :parent [org.clojure/pom.contrib "0.0.25"]

  :jvm-opts ^:replace ["-Xmx512m" "-server"]

  :source-paths ["src/main/clojure"]
  :dependencies [[org.clojure/clojure "1.7.0" :scope "provided"]
                 [org.clojure/clojurescript "0.0-3308" :scope "provided"]
                 [org.clojure/tools.macro "0.1.2"]
                 ;[com.datomic/datomic-free "0.8.4270" :scope "provided"]
                 ]

  :clean-targets ^{:protect false} ["resources/tests.js" "resources/out"])
