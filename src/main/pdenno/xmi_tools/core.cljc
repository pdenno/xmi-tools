(ns pdenno.xmi-tools.core ; POD maybe a better name would be uml_mm. 
  "Parse XMI for a UML metamodel." 
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
(defonce wconn nil) ; "The connection to the database"
(defonce bad-file-on-rebuild? (atom #{})) ; For debugging

;;; :db/db.cardinality=many means value is a vector of values of some :db.type. Orthogonal to dd.type/ref. 
(def work-schema
  "Defines the datahike schema for this throw-away database used to construct a MOF-based model. 
   The following are only the ones that aren't learned from the schema. (See update-mof-keys)."
  [#:db{:cardinality :db.cardinality/one,  :valueType :db.type/keyword, :ident :meta/property}
   #:db{:cardinality :db.cardinality/many, :valueType :db.type/ref,     :ident :meta/content}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :meta/string-content}
   #:db{:cardinality :db.cardinality/many, :valueType :db.type/keyword, :ident :meta/mof-keys}

   #:db{:cardinality :db.cardinality/many, :valueType :db.type/ref,     :ident :model/content}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/id}   
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/name}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/keyword, :ident :model/type}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/URI}

   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/type}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/id :unique :db.unique/identity}])

(def resolve-props #{:mof/annotatedElement :mof/general})

(defn mm-find-instance
  "Find an instance (in the working schema?) using one any of the means provided by the keyword args:
         all? - return a vector of all matching if true. 
         type - a string naming a type
         name - the name of the object, for example, if :type-name 'uml:Class' then 'NamedElement' etc.
         db - the db-connection, defaults to atom on var wconn.
         predicate - first found where it is true  (NYI)

  Returns the db-id of the object."
  [& {:keys [predicate type xmi-id name model db model db all?] :or {db wconn}}]
  (let [v '?e
        qvar (if all? (vector (vector v '...)) (vector v '.))]
    (cond (and type xmi-id)
          (d/q `[:find ~@qvar :where [~v :xmi/type ~type] [~v :xmi/id ~xmi-id]] @db),
          xmi-id
          (d/q `[:find ~@qvar :where [~v :xmi/id ~xmi-id]] @db),
          type
          (d/q `[:find ~@qvar :where [~v :xmi/type ~type]] @db))))

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

(defn find-mof-keys
  "Return a set of the property names that don't have a namespace."
  [model]
  (let [mof-keys-atm (atom #{})]
    (walk/postwalk ; Collect keys that aren't ns-qualified.
     (fn [x] 
       (when (map? x) (swap! mof-keys-atm (fn [mk] (into mk (remove namespace (keys x))))))
       x)
     model)
    @mof-keys-atom))

(defn add-mof-keys
  "We only use ns-qualified keys in DH DBs. The unqualified ones in the working schema
   at the time this called are MOF concepts. Later some with the same base name will be
   created specialized to the namespace of each Element that defines it."
  [model mof-key?]
  (let [mof-key? (:meta/mof-keys model)]
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
     model)))

;;; POD Could probably replace this with specific information:
;;; {"isAbstract" {:db.type :db.type/boolean :specific/name <whatever defines isAbstract>}
;;; Problem is, the same names property could be defined in more than one place. (Check "name", for example.)
;;; On second thought, are these things actually MOF properties? (It seems describing a metamodel would require these!)

(def mof-boolean?  #{:mof/isAbstract :mof/isDerived :mof/isDerivedUnion :mof/isOrdered :mof/isQuery
                    :mof/isReadOnly :mof/isUnique})
(def mof-keywordable? #{:mof/aggregation :mof/direction})
(def mof-resolvable? #{:mof/annotatedElement :mof/association :mof/bodyCondition :mof/constrainedElement
                       :mof/general :mof/importedPackage :mof/instance :mof/memberEnd :mof/precondition
                       :mof/redefinedOperation :mof/redefinedProperty :mof/subsettedProperty :mof/type})
(def mof-other? #{:mof/URI :mof/href :mof/language :mof/name :mof/value})

(defn mof-db-schema
  "Return a vector of DH schema entries for the learned MOF db attributes."
  [mof-keys]
  (for [x mof-keys]
    (let [val-type (cond (mof-boolean? x)     :db.type/boolean
                         (mof-keywordable? x) :db.type/keyword
                         (mof-resolvable? x)  :db.type/ref
                         (mof-other? x)       :db.type/string
                         :else (log/error "Unknown mof key:" x))]
      {:db/cardinality :db.cardinality/one, :db/valueType val-type :db/ident x})))

;;; See comment above. Maybe I could inspect precedence list to know who defines what. 
(defn resolve-mof-keys
  "For use prior to storing in DH: Certain MOF properties, identified as keywords in the namespace 'mof',
  are strings that reference object-type things, others such properties have keyword or boolean values. 
   This returns a map with the objects resolved to {:db/id <num>} or booleans or keywords."
  [model]
  :NYI) ;<========================================================================================================================================== POD POD POD POD

;;; POD Revisit the problem described in the defn doc string. This won't be a problem with a working DB
;;;     that is fresh for each MM. 
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

;;; (xml2mofy :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
(defn xml2mofy
  "Read and process file to something that can be temporarily stored in DH for
   subsequent generation of the metamodel."
  [& {:keys [path shortname]}]
  (as-> (util/read-clean path) ?m
    (deXML-ize ?m)
    (assoc ?m :meta/mof-keys (find-mof-keys ?m))
    (add-mof-keys ?m)
    (resolve-mof-keys ?m)
    #_(update-xmi-id ?m shortname))) ; POD This can probably wait until the permanent DB!

;;; (add-work-file :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
(defn add-work-file
  "Throw schema into a temporary DB used for construct MOF-based metaobjectfor reconstruction."
  [& {:keys [path shortname] :or {path "resources/schema/uml-2.4.1.xmi" shortname "uml241"}}]
  (let [model (xml2mofy :path path :shortname shortname)
        db-schema (into work-schema (mof-db-schema (:meta/mof-keys model))) 
        db-content [{:model/name shortname
                     :model/type (:meta/property model)
                     :model/id   (:xmi/id model)
                     :model/URI  (:mof/URI model)
                     :model/content (:meta/content model)
                     :meta/mof-keys (vec (:meta/mof-keys model))}]]
    (try
      (if (util/storable? db-content db-schema)
        (try
          (d/transact wconn db-schema)  ; transact the schema; part of it is learned. 
          (d/transact wconn db-content) ; Use d/transact here, not transact! which uses a future.
             (catch Exception e
               (swap! bad-file-on-rebuild? conj path)
               (log/error "Error adding" path ":" (-> e str (subs 0 200)))))
        (do (swap! bad-file-on-rebuild? conj path)
            (reset! diag db-content)
            (log/error "Schema-map contains nils and cannot be stored." path)))
      (catch Exception e
        (swap! bad-file-on-rebuild? conj path)
        (log/error "Error checking storable?" path ":" e)))))

;;; (get-model "uml241" wconn)
(defn get-model
  "Return the map stored in the database for the given schema-urn. Useful in development."
  [shortname wconn & {:keys [resolve? filter-set] :or {resolve? true filter-set #{}}}]
  (when-let [ent  (d/q `[:find ?ent .
                         :where [?ent :model/name ~shortname]] @wconn)]
    (cond-> (dp/pull @wconn '[*] ent)
      resolve? (util/resolve-db-id wconn filter-set))))

(defn class-ent
  "Return the :db/id of the named class."
  [class-name wconn]
  (d/q `[:find ?e . :where [?e :xmi/type "uml:Class"] [?e :mof/name ~class-name]] @wconn))

(defn class-attr-ents
  "Return a vector of the :db/id of the named class."
  [class-ent wconn]
  (d/q `[:find [?e ...] :where
         [~class-ent :meta/content ?e]
         [?e :meta/property :ownedAttribute]]
       @wconn))

(defn attr-name
  "Return the name (a string) of the attr given its :db/id."
  [attr-ent wconn]
  (d/q `[:find ?t . :where [~attr-ent :mof/name ?t]]
       @wconn))

(defn attr-type
  "Return the type (a string) of the attr given its :db/id."
  [attr-ent wconn]
  (d/q `[:find ?t . :where [~attr-ent :mof/type ?t]]
       @wconn))

(defn attr-association
  "Return the assocation (a string) of the attr given its :db/id."
  [attr-ent wconn]
  (d/q `[:find ?t . :where [~attr-ent :mof/association ?t]]
       @wconn))

(defn attr-subsetted
  "Return the type (a string) of the attr given its :db/id."
  [attr-ent wconn]
  (d/q `[:find ?p . :where [~attr-ent :mof/subsettedProperty ?p]]
       @wconn))


(defn attr-multiplicity
  "Return a map about the upper multiplicity of the attr given its :db/id."
  [attr-ent wconn upper-lower?] ; POD spec #{:upperValue :lowerValue}. 
  (let [content (d/q `[:find ?cnt . :where 
                         [~attr-ent :meta/content ?cnt]
                         [?cnt      :meta/property ~upper-lower?]]  @wconn)
        val (d/q `[:find ?v . :where
                         [~content :mof/value ?v]] @wconn)
        type (d/q `[:find ?t . :where
                          [~content :xmi/type ?t]] @wconn)]
    (cond-> {}
      val  (assoc :value val)
      type (assoc :type  type))))

(defn ent-comments
  "Return a vector of the comments on an object."
  [ent wconn]
  (d/q `[:find [?c ...] :where
         [~ent  :meta/content ?cnt]
         [?cnt  :meta/property :ownedComment]
         [?cnt  :meta/content ?cnt2]
         [?cnt2 :meta/string-content ?c]]
       @wconn))

;;; ==================> ToDo attribute composite, opposite. readonly, derived, derived-union <======================
;;; It would be good to be able to default things in d/q. Possible? ...No, I don't think so. 
(defn construct-attr
  "Given an attribute :db/id, return all information about the attribute as a map."
  [attr-ent wconn]
  (let [typ (attr-type attr-ent wconn)
        subsetted (attr-subsetted attr-ent wconn)]
    (as-> {:attr/name (attr-name attr-ent wconn)} ?a
      (assoc ?a :attr/ownedComment (apply str (ent-comments attr-ent wconn)))
      (if typ (assoc ?a :attr/type typ) ?a)
      (if subsetted (assoc ?a :attr/subsets subsetted) ?a)
      (assoc ?a :attr/multiplicity {:attr/lowerValue (attr-multiplicity attr-ent wconn :lowerValue)
                                    :attr/upperValue (attr-multiplicity attr-ent wconn :upperValue)}))))

(defn construct-class
  "Given a class name, return all information about the class as a map."
  [class-name wconn]
  (let [class-ent (class-ent class-name wconn)
        attr-ents (class-attr-ents class-ent wconn)]
    (as-> {:class/name class-name} ?c
      (assoc ?c :class/ownedComment (apply str (ent-comments class-ent wconn)))
      (assoc ?c :class/ownedAttribute (->> (map #(construct-attr % wconn) attr-ents)
                                           (sort-by :attr/name)
                                           vec)))))


(defn refresh-conn [] (alter-var-root (var wconn) (fn [_] (d/connect db-cfg))))

;;;================================ Starting and Stopping ===========================================
;;; (user/restart) whenever you update the DB or the resolvers. (tools/refresh) if compilation fails.

(defn create-db!
  "Create the database if :rebuild? is true, otherwise just set the connection atom, wconn."
  []
  (cond (:rebuild-db? db-cfg)
        (binding [log/*config* (assoc log/*config* :min-level :info)]
          (reset! bad-file-on-rebuild? #{})
          (when (d/database-exists? db-cfg) (d/delete-database db-cfg))
          (d/create-database db-cfg)
          (alter-var-root (var wconn) (fn [_] (d/connect db-cfg)))
          #_(add-work-file :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
          (add-work-file :path "resources/schema/uml25-validator-verbatim.xmi" :shortname "uml25")
          (log/info "Created schema DB")),
        (d/database-exists? db-cfg) (alter-var-root (var wconn) (fn [_] (d/connect db-cfg))),
        :else (log/warn "There is no DB to connect to.")))

(defstate core
  :start
  (do (create-db!) db-cfg))
