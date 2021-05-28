(ns pdenno.xmi-tools.core
  "Parse XMI."
  (:refer-clojure :exclude [slurp])
  (:require
   [clojure.edn            :as edn]
   [clojure.pprint         :refer [cl-format]]
   [clojure.string         :as str]
   [clojure.set            :as sets]
   [malli.core             :as m]
   [pdenno.xmi-tools.utils :as util]
   [taoensso.timbre        :as log]))

(defn read-clean
  "Return a map structure containing the :xml/content (cleaned-up) and :ns-info."
  [pathname]
  (let [xml (util/read-xml pathname)]
    xml))

;;; Maybe the plan for message-mapper is to store message schema as CCTS UML (using Model3).
;;; This experimentation might be the start of that.

;;; (tryme "resources/test-files/model3-with-profile.xml")
(defn tryme
  "I experiment with getting XMI ready for Malli and Datahike."
  [& {:keys [path] :or {path "resources/test-files/model3-with-profile.xml"}}]
  (-> path read-clean #_rewrite-xmi #_util/condition-form #_vector))


