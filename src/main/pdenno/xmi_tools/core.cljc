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
   [pdenno.xmi-tools.utils :as util :refer [qconnect]]
   [taoensso.timbre        :as log]))

(def db-cfg {:store {:backend :mem, :id "working-db"}, ; :id could be "uml25" if things are too slow.
             :mine/rebuild-db? true
             :keep-history? false
             :schema-flexibility :write})

#_(def db-cfg {:store {:backend :file :path "resources/database"}
             :mine/rebuild-db? true
             :schema-flexibility :write})


(def diag (atom nil))
(defonce bad-file-on-rebuild? (atom #{})) ; For debugging

;;; :db/db.cardinality=many means value is a vector of values of some :db.type. Orthogonal to dd.type/ref. 
(def work-schema
  "Defines the datahike schema for this throw-away database used to construct a MOF-based model. 
   The following are only the ones that aren't learned from the schema. (See find-mof-keys)."
  [#:db{:cardinality :db.cardinality/many, :valueType :db.type/ref,     :ident :meta/content}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/ref,     :ident :meta/owner} ; Owner in XML sense. 
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/keyword, :ident :meta/property}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :meta/shortname} ; Only the model has this. (e.g. "uml25")  
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :meta/string-content}

   ;; These will be retracted and replaced with :db/id
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/annotatedElement}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/association}   
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/bodyCondition}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/constrainedElement}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/general}   
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/importedPackage}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/instance}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/memberEnd}   
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/precondition}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/redefinedOperation}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/redefinedProperty}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/subsettedProperty}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :temp/type}

   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/type}
   #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :xmi/id :unique :db.unique/identity}])

(def resolve-props #{:mof/annotatedElement :mof/general})

(defn mm-find-instance
  "Find an instance (in the working schema?) using one any of the means provided by the keyword args:
         all? - return a vector of all matching if true. 
         type - a string naming a type
         xmi-id - the xmi-id from the XMI file. 
         name - the name of the object, (might just be for NamedElement???). 
         predicate - first found where it is true  (NYI)

  Returns the db-id of the object."
  [& {:keys [predicate type xmi-id name model model all?]}]
  (let [conn (qconnect db-cfg)
        v '?e
        qvar (if all? (vector (vector v '...)) (vector v '.))]
    (cond (and type xmi-id)
          (d/q `[:find ~@qvar :where [~v :xmi/type ~type] [~v :xmi/id ~xmi-id]] @conn),
          xmi-id
          (d/q `[:find ~@qvar :where [~v :xmi/id ~xmi-id]] @conn),
          type
          (d/q `[:find ~@qvar :where [~v :xmi/type ~type]] @conn))))

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

;;; POD Could probably replace this with specific information:
;;; {"isAbstract" {:db.type :db.type/boolean :specific/name <whatever defines isAbstract>}
;;; Are these things actually MOF properties? (It seems describing a metamodel would require these!)

;;; The following were found by running util/find-mof-keys. 
(def mof-boolean?  #{:isAbstract :isDerived :isDerivedUnion :isOrdered :isQuery :isReadOnly :isUnique})
(def mof-keywordable? #{:aggregation :direction})
(def mof-resolvable? #{:annotatedElement :association :bodyCondition :constrainedElement
                       :general :importedPackage :instance :memberEnd :precondition
                       :redefinedOperation :redefinedProperty :subsettedProperty :type})
(def mof-other? #{:URI :href :language :name :value})
(def mof-keys? "This one is just to make the DH DB schema."
  (reduce (fn [super sub] (into super sub))
          #{}
          [mof-boolean? mof-keywordable? mof-resolvable? mof-other?]))
(def mof-temp-resolvable?
  "These are attributes with string values. The attribute will be retracted and replaced with a db/id."
  (reduce (fn [s v] (conj s (keyword "temp" (name v)))) #{} mof-resolvable?))

;;; "A_attribute_classifier-classifier A_ownedAttribute_structuredClassifier-structuredClassifier NamedElement-namespace"
(def mof-temp-resolvable-special?
  "These have string values with multiple (2 or 3?) components separated by spaces; the '-' matters too!"
  #{:temp/redefinedProperty :temp/redefinedOperation :temp/constrainedElement :temp/memberEnd :temp/subsettedProperty})

(defn mof-db-schema
  "Return a vector of DH schema entries for the learned MOF db attributes."
  [mof-keys]
  (for [x mof-keys]
    (let [val-type (cond (mof-boolean? x)     :db.type/boolean
                         (mof-keywordable? x) :db.type/keyword
                         (mof-resolvable? x)  :db.type/ref
                         (mof-other? x)       :db.type/string
                         :else (log/warn "Unknown mof key (1):" x))]
      {:db/cardinality :db.cardinality/one, :db/valueType val-type :db/ident (keyword "mof" (name x))})))

(defn coerce-mof-vals
  "For use BEFORE storing in DH: Certain MOF properties, identified as keywords in the namespace 'mof',
   are strings that reference object-type things, others such properties have keyword or boolean values. 
   This returns a map with the objects resolved to {:db/id <num>} or booleans or keywords."
  [model]
  (walk/postwalk
   (fn [x]
     (if (map? x)
       (reduce-kv (fn [m k v]
                    (if (not (namespace k))
                      (let [qk (keyword "mof" (name k))]
                        (cond (mof-boolean? k)
                              (let [v (k x)]
                                    (cond (= v "true")  (assoc m qk true), 
                                          (= v "false") (assoc m qk false)
                                          :else (do (log/warn "Expected a Boolean for" k "value is " v) m))),
                            
                                (mof-keywordable? k) 
                                (if (string? v)
                                  (assoc m qk (keyword v))
                                  (do (log/warn "Expecetd a keyword string for" k "value is" v) m)),
                            
                                (mof-resolvable? k) ; These temp ones will be retracted and replaced with refs. 
                                (assoc m (keyword "temp" (name k)) v)
                                
                                (mof-other? k) (assoc m qk v), 
                                
                                :else (do (log/warn "Unknown mof key (2):" k) m)))
                      (assoc m k v)))
                  {}
                  x)
       x))
   model))

(defn resolve-mof-refs!
  "For use AFTER storing in DH: replace :temp/<whatever> strings with the :db/id to which they refer."
  []
  (binding [log/*config* (assoc log/*config* :min-level :info)]
    (let [conn (qconnect db-cfg)]
      (doseq [prop mof-temp-resolvable? ; Choice of key names matters! Can produce a bug!
              ent-val (d/q `[:find ?e ?v :keys mm/ee mm/vv :where [?e ~prop ?v]] @conn)]
        (when-not (mof-temp-resolvable-special? prop)
          (if-let [ref (d/q `[:find ?e . :where [?e :xmi/id ~(:mm/vv ent-val)]] @conn)]
            (d/transact conn [[:db.fn/retractAttribute (:mm/ee ent-val) prop]
                              [:db/add (:mm/ee ent-val) (keyword "mof" (name prop)) ref]])
            (log/warn "Could not find reference for" ent-val "property =" prop)))))))
    
(defn set-owner!
  "Set the owning entity (in the XMI sense), :mof/owner in the DB."
  []
  (binding [log/*config* (assoc log/*config* :min-level :info)]
    (let [conn (qconnect db-cfg)]
      (doseq [xmi-obj (d/q '[:find [?e ...] :where [?e :xmi/id _]] @conn)]
        (if-let [owner (d/q `[:find ?e . :where [?e :meta/content ~xmi-obj]] @conn)]
          (d/transact conn [[:db/add xmi-obj :meta/owner owner]])
          (log/info "Does not have an owner (Probably top level):" xmi-obj))))))
  
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

;;; (xml2mofy :path "resources/schema/uml25-validator-verbatim.xmi" :shortname "uml25")
(defn xml2mofy
  "Read and process file to something that can be temporarily stored in DH for
   subsequent generation of the metamodel."
  [& {:keys [path]}]
  (as-> (util/read-clean path) ?m
    (deXML-ize ?m)
    (coerce-mof-vals ?m)))

;;; (add-metamodel :path "resources/schema/uml25-validator-verbatim.xmi" :shortname "uml25")
(defn add-metamodel
  "Throw schema into a temporary DB used for construct MOF-based metaobjectfor reconstruction."
  [& {:keys [path shortname]}]
  (let [conn (qconnect db-cfg)
        model (-> (xml2mofy :path path) (assoc :meta/shortname shortname))
        db-schema (into work-schema (mof-db-schema mof-keys?)) 
        db-content (vector model)]
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

;;; (get-model "uml25")
(defn get-model
  "Return the map stored in the database for the given schema-urn. Useful in development."
  [shortname]
  (let [[ent typ] (d/q `[:find [?e ?t] :where 
                         [?e :meta/shortname ~shortname]
                         [?e :xmi/type ?t]] @(qconnect db-cfg))]
    {:type typ :id ent}))

;;;; This is WIP. Too slow! Use dp/pull !
(defn get-object
  "Create a map about the object that goes only one step deeper."
  [id & {:keys [just-name?]}]
  (let [conn (qconnect db-cfg)
        typ (d/q `[:find ?t . :where  [~id :xmi/type ?t]] @conn)
        nam (d/q `[:find ?n . :where  [~id :mof/name ?n]] @conn)
        cnt (when-not just-name? (d/q `[:find [?c ...] :where  [?c :meta/owner ~id]] @conn))]
    (cond-> {:type typ :id id}
      nam              (assoc :mof/name nam)
      (not just-name?) (assoc :meta/content (mapv #(get-object % :just-name? true) cnt)))))

(defn class-ent
  "Return the :db/id of the named class."
  [class-name]
  (d/q `[:find ?e . :where [?e :xmi/type "uml:Class"] [?e :mof/name ~class-name]] @(qconnect db-cfg)))

(defn class-attr-ents
  "Return a vector of the :db/id of the named class."
  [class-ent]
  (d/q `[:find [?e ...] :where
         [~class-ent :meta/content ?e]
         [?e :meta/property :ownedAttribute]]
       @(qconnect db-cfg)))

(defn attr-name
  "Return the name (a string) of the attr given its :db/id."
  [attr-ent]
  (d/q `[:find ?t . :where [~attr-ent :mof/name ?t]] @(qconnect db-cfg)))

(defn attr-type
  "Return the type (a string) of the attr given its :db/id."
  [attr-ent]
  (d/q `[:find ?t . :where [~attr-ent :mof/type ?t]] @(qconnect db-cfg)))

(defn attr-association
  "Return the assocation (a string) of the attr given its :db/id."
  [attr-ent]
  (d/q `[:find ?t . :where [~attr-ent :mof/association ?t]] @(qconnect db-cfg)))

(defn attr-subsetted
  "Return the type (a string) of the attr given its :db/id."
  [attr-ent]
  (d/q `[:find ?p . :where [~attr-ent :mof/subsettedProperty ?p]] @(qconnect db-cfg)))


(defn attr-multiplicity
  "Return a map about the upper multiplicity of the attr given its :db/id."
  [attr-ent upper-lower?] ; POD spec #{:upperValue :lowerValue}. 
  (let [conn (qconnect db-cfg)
        content (d/q `[:find ?cnt . :where 
                         [~attr-ent :meta/content ?cnt]
                         [?cnt      :meta/property ~upper-lower?]]  @conn)
        val (d/q `[:find ?v . :where
                         [~content :mof/value ?v]] @conn)
        type (d/q `[:find ?t . :where
                          [~content :xmi/type ?t]] @conn)]
    (cond-> {}
      val  (assoc :value val)
      type (assoc :type  type))))

(defn ent-comments
  "Return a vector of the comments on an object."
  [ent]
  (d/q `[:find [?c ...] :where
         [~ent  :meta/content ?cnt]
         [?cnt  :meta/property :ownedComment]
         [?cnt  :meta/content ?cnt2]
         [?cnt2 :meta/string-content ?c]]
       @(qconnect db-cfg)))

;;; ==================> ToDo attribute composite, opposite. readonly, derived, derived-union <======================
;;; It would be good to be able to default things in d/q. Possible? ...No, I don't think so. 
(defn construct-attr
  "Given an attribute :db/id, return all information about the attribute as a map."
  [attr-ent]
  (let [typ (attr-type attr-ent)
        subsetted (attr-subsetted attr-ent)]
    (as-> {:attr/name (attr-name attr-ent)} ?a
      (assoc ?a :attr/ownedComment (apply str (ent-comments attr-ent)))
      (if typ (assoc ?a :attr/type typ) ?a)
      (if subsetted (assoc ?a :attr/subsets subsetted) ?a)
      (assoc ?a :attr/multiplicity {:attr/lowerValue (attr-multiplicity attr-ent :lowerValue)
                                    :attr/upperValue (attr-multiplicity attr-ent :upperValue)}))))

(defn construct-class
  "Given a class name, return all information about the class as a map."
  [class-name]
  (let [class-ent (class-ent class-name)
        attr-ents (class-attr-ents class-ent)]
    (as-> {:class/name class-name} ?c
      (assoc ?c :class/ownedComment (apply str (ent-comments class-ent)))
      (assoc ?c :class/ownedAttribute (->> (map construct-attr attr-ents)
                                           (sort-by :attr/name)
                                           vec)))))

;;;================================ Starting and Stopping ===========================================
;;; (user/restart) whenever you update the DB or the resolvers. (tools/refresh) if compilation fails.

(defn create-db!
  "Create the database if :rebuild? is true."
  []
  (when (:mine/rebuild-db? db-cfg)
    (binding [log/*config* (assoc log/*config* :min-level :info)]
      (reset! bad-file-on-rebuild? #{})
      (when (d/database-exists? db-cfg) (d/delete-database db-cfg))
      (d/create-database db-cfg)
      (log/info "Starting DB rebuild")
      #_(add-metamodel :path "resources/schema/uml-2.4.1.xmi" :shortname "uml241")
      (add-metamodel :path "resources/schema/uml25-validator-verbatim.xmi" :shortname "uml25")
      (resolve-mof-refs!)
      (set-owner!)
      (log/info "Ending DB rebuild (except for futures)")      
      (log/info "Created schema DB"))))

(defstate core
  :start
  (do (create-db!) db-cfg))
