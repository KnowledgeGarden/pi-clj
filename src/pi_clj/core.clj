(ns pi-clj.core
  (:gen-class)
  (:require [pi-clj.wts :as wts]))



;; Main entry point
(defn -main
  "Run PI Wave Theory of Sound."
  [& args]
  (wts)
  (println "Did!"))
