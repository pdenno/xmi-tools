(ns pdenno.xmi-tools.core
  "Parse XMI."
  (:refer-clojure :exclude [slurp])
  (:require
   [clojure.string         :as str]
   [clojure.walk           :as walk]
   [datahike.api           :as d]
   [datahike.pull-api      :as dp]
   [malli.core             :as m]
   [mount.core             :refer [defstate]]
   [pdenno.xmi-tools.utils :as util]
   [taoensso.timbre        :as log]))

(def db-cfg {:store {:backend :mem, :id "working-db"}, #_{:backend :file :path "resources/database"}
             :rebuild-db? true
             :schema-flexibility :write})

(def diag (atom nil))
(defonce conn nil) ; "The connection to the database"
(defonce bad-file-on-rebuild? (atom #{})) ; For debugging

;;; :db/db.cardinality=many means value is a vector of values of some :db.type. Orthogonal to dd.type/ref. 
(def work-schema
  "Defines the datahike schema for this throw-away database used to construct a MOF-based model. 
   The following are only the ones that aren't learned from the schema. (See update-mof-keys)."
  [#:db{:cardinality :db.cardinality/one,  :valueType :db.type/keyword, :ident :meta/property}
   #:db{:cardinality :db.cardinality/many, :valueType :db.type/ref,     :ident :meta/content}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :meta/string-content}

   #:db{:cardinality :db.cardinality/many, :valueType :db.type/ref,     :ident :model/content}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/id}   
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/name}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/keyword, :ident :model/type}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/URI}

   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/type}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/id :unique :db.unique/identity}])

(defn deXML-ize
  "Turn the xml-looking obj into a map that has MOF characteristics."
  [obj]
  (cond (not (map? obj)) obj,
        ;; Every other string in the file is a string object. <body> and <language> are not.
        ;; So it isn't surprising that this is messed up. 
        (#{:body :language} (:xml/tag obj))
        (-> obj
            (assoc  :meta/string-content (apply str (:xml/content obj)))
            (assoc  :meta/property (:xml/tag obj))
            (dissoc :xml/tag :xml/content)),
        :else
        (as-> obj ?o
          (if (contains? ?o :xml/tag)     (assoc ?o :meta/property (:xml/tag obj))     ?o)
          (if (contains? ?o :xml/attrs)   (reduce-kv (fn [m k v] (assoc m k v)) ?o (:xml/attrs ?o)) ?o)
          (if (contains? ?o :xml/content) (assoc ?o :meta/content (mapv deXML-ize (:xml/content ?o))) ?o)
          (dissoc ?o :xml/content :xml/tag :xml/attrs))))

(defn update-mof-keys
  "We only use ns-qualified keys in DH DBs. The unqualified ones in the working schema
   at the time this called are MOF concepts. Later some with the same base name will be
   created specialized to the namespace of each Element that defines it.
   Also sets :mof-keys in model."
  [model]
  (let [mof-keys-atm (atom #{})
        mof-key? (do (walk/postwalk ; Collect keys that aren't ns-qualified.
                      (fn [x] 
                        (when (map? x) (swap! mof-keys-atm (fn [mk] (into mk (remove namespace (keys x))))))
                        x)
                      model)
                     @mof-keys-atm)]
    (-> ; ns-qualify unqualified keys as ":mof/<whatever>". 
     (walk/postwalk
      (fn [x]
        (if (map? x)
          (reduce-kv (fn [m k v]
                       (if (mof-key? k)
                         (assoc m (keyword "mof" (name k)) v)
                         (assoc m k v)))
                     {}
                     x)
          x))
      model)
     ;; Could have done the above with one walk, but I need :mof-keys for later. 
     (assoc :mof-keys mof-key?))))
  
(defn update-xmi-id
  "xmi-id of UML specs use computed names that will likely be the same
   from one spec to the next. That's not good for a DH :db.unique/identity."
  [model shortname]
  (walk/postwalk
   (fn [x]
     (if (and (map? x) (contains? x :xmi/id))
       (update x :xmi/id #(str shortname ":" %))
       x))
   model))

(defn mof-db-schema
  "Return a vector of DH schema entries for the learned MOF db attributes."
  [model]
  (for [x (:mof-keys model)]
    (assoc #:db{:cardinality :db.cardinality/one, :valueType :db.type/string}
           :db/ident (keyword "mof" (name x)))))

;;; (xml2mofy :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
(defn xml2mofy
  "Read and process file to something that can be temporarily stored in DH for
   subsequent generation of the metamodel."
  [& {:keys [path shortname]}]
  (let [model (-> (util/read-clean path) 
                  deXML-ize
                  update-mof-keys
                  (update-xmi-id shortname))] ; POD This can probably wait until the permanent DB!
    model))

;;; (add-work-file :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
(defn add-work-file
  "Throw schema into a temporary DB used for construct MOF-based metaobjectfor reconstruction."
  [& {:keys [path shortname] :or {path "resources/schema/uml-2.4.1.xmi" shortname "uml241"}}]
  (let [model (xml2mofy :path path :shortname shortname)
        db-schema (into work-schema (mof-db-schema model)) 
        db-content [{:model/name shortname
                     :model/type (:meta/property model)
                     :model/id   (:xmi/id model)
                     :model/URI  (:mof/URI model)
                     :model/content (:meta/content model)}]]
    (try
      (if (util/storable? db-content db-schema)
        (try
          (d/transact conn db-schema)  ; transact the schema; part of it is learned. 
          (d/transact conn db-content) ; Use d/transact here, not transact! which uses a future.
             (catch Exception e
               (swap! bad-file-on-rebuild? conj path)
               (log/error "Error adding" path ":" (-> e str (subs 0 200)))))
        (do (swap! bad-file-on-rebuild? conj path)
            (reset! diag db-content)
            (log/error "Schema-map contains nils and cannot be stored." path)))
      (catch Exception e
        (swap! bad-file-on-rebuild? conj path)
        (log/error "Error checking storable?" path ":" e)))))

(defn refresh-conn [] (alter-var-root (var conn) (fn [_] (d/connect db-cfg))))

;;;================================ Starting and Stopping ===========================================
;;; (user/restart) whenever you update the DB or the resolvers. (tools/refresh) if compilation fails.

(defn create-db!
  "Create the database if :rebuild? is true, otherwise just set the connection atom, conn."
  []
  (cond (:rebuild-db? db-cfg)
        (binding [log/*config* (assoc log/*config* :min-level :error)] ; Was :info. 
          (reset! bad-file-on-rebuild? #{})
          (when (d/database-exists? db-cfg) (d/delete-database db-cfg))
          (d/create-database db-cfg)
          (alter-var-root (var conn) (fn [_] (d/connect db-cfg)))
          (add-work-file :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
          (log/info "Created schema DB")),
        (d/database-exists? db-cfg) (alter-var-root (var conn) (fn [_] (d/connect db-cfg))),
        :else (log/warn "There is no DB to connect to.")))

(defstate core
  :start
  (do (create-db!) db-cfg))
