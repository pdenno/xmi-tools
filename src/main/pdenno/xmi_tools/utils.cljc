(ns pdenno.xmi-tools.utils
  "Utilities for XMI parsing and rewriting."
  (:require
   [cemerick.url                 :as url]
   [clojure.data.xml             :as x]
   [clojure.java.io              :as io]
   [clojure.string               :as str]
   [taoensso.timbre              :as log]
   [clojure.walk                 :as walk]))

;;;================================== POD THIS PROBABLY GOES AWAY WHEN I use xmi-tools as a library (borrowed from messge-mapper) ===========================

(defn keywordize
  "Return the string as a keyword. If the string as a colon in it,
  the prefix is used as the keyword's namespace."
  ([str]
   (if (string? str)
     (if-let [[_ prefix word] (re-matches #"(\w+)\:(\w+)" str)]
       (keyword prefix word)
       (keyword str))
     str))
  ([str ns]
    (keyword ns str)))

(def keywords?
  "A set of map keys corresponding to values that should be keywordized"
  #{})

(def needs-zip?
  "A set of map keys where I need to encode a map for later decoding (See db-utils/resolve-db-id)"
  #{})

(defn condition-form
  "Return the form with certain map values as keywords and certain map values zipped."
  [form & {:keys [key-pred] :or {key-pred keywords?}}]
  (cond (map? form) (reduce-kv (fn [m k v]
                                 (if (needs-zip? k)
                                   (-> m
                                       (assoc :zip/keys (-> v keys vec))
                                       (assoc :zip/vals (-> v vals vec)))
                                   (if (key-pred k)
                                     (assoc m k (keywordize v))
                                     (assoc m k (condition-form v)))))
                                 {}
                                 form)
        (vector? form)   (mapv condition-form form)
        (set? form) (set (map  condition-form form))
        (coll? form)     (map  condition-form form)
        :else form))

;;; #:db{:cardinality :db.cardinality/one,  :valueType :db.type/string,  :ident :model/URI}
(defn storable?
  "Check that the object
   (1) is not nil,
   (2) if it is a map, that the values of all keys are conforming.
   (3) if it is a collection, that all of its
   Such data cannot be stored in datahike."
  [obj db-schema]
  (let [ok? (atom true)
        db-map (zipmap (map :db/ident db-schema) db-schema)]
    (letfn [(val-ok? [v typ]
              (cond (= typ :db.type/string)  (string?  v),
                    (= typ :db.type/boolean) (boolean? v),
                    (= typ :db.type/keyword) (keyword? v),
                    (= typ :db.type/ref)     (map?     v),
                    (#{:db.type/bigdec :db.type/bigint :db.type/double :db.type/float :db.type/long :db.type/number} typ) (number? v),
                    :else true)) ; POD I grow weary. 
            (valid-val? [k v]
              (if-let [spec (get db-map k)]
                (or (and (case (:db/cardinality spec)
                           :db.cardinality/one  (not (coll? v))
                           :db.cardinality/many (vector? v))
                         (if (= (:db/cardinality spec) :db.cardinality/many)
                           (every? #(val-ok? % (:db/valueType spec)) v)
                           (val-ok? v (:db/valueType spec))))
                    (log/error "Expected a value conforming to" spec "\n got" (subs (str v) 0 100) "..."))
                (log/error (subs (str v) 0 100) "...is not a schema type.")))
            (storable-aux [obj]
              (cond (not @ok?) false
                    (nil? obj) (reset! ok? false)
                    (map? obj) (reset! ok? (reduce-kv (fn [result k v] (cond (not @ok?) false
                                                                             (not result) false
                                                                             (nil? v) false
                                                                             :else
                                                                             (and (valid-val? k v) 
                                                                                  (storable-aux v))))
                                                      true
                                                      obj))
                    ;; POD should I be checking the types of values here, rather than the :else true? 
                    (coll? obj) (reset! ok? (every? storable-aux obj))
                    :else true))]
      (storable-aux obj))
    @ok?))

(defn remove-nils
  "Return the object with nils removed. USE OF THIS DISCOURAGED."
  [obj]
  (let [pname (:schema/pathname obj)]
    (letfn [(remove-nils-aux [obj]
              (walk/prewalk
               (fn [obj]
                 (cond (map? obj) (reduce-kv (fn [m k v]
                                               (cond (nil? k) (do (log/info "nil key in map, value=" v "file=" pname) m)
                                                     (nil? v) (do (log/info "nil val in map, key=" k "file=" pname) m)
                                                     :else (assoc m k v)))
                                             {}
                                             obj)
                       (vector? obj) (mapv remove-nils-aux obj)
                       (set? obj)    (set (map remove-nils-aux obj))
                       (coll?   obj) (map remove-nils-aux obj)
                       (nil? obj)    (do (log/info "nil value replaced." "file=" pname) :mm/nil)
                       :else obj))
               obj))]
      (remove-nils-aux obj))))
           
(defn clean-whitespace
  "Remove whitespace in element :content."
  [xml]
  (walk/postwalk
   (fn [obj]
     (if (and (map? obj) (contains? obj :content))
       (if (= 1 (count (:content obj))) ;; POD Maybe don't remove it if is the only content???
         obj
         (update obj :content (fn [ct] (remove #(and (string? %) (re-matches #"^\s*$" %)) ct))))
       obj))
   xml))

;;; POD This is updated since borrowed from message-mapper/utils.cljs.
;;; It is percent-encoding (url/url-encode) and keywordizes the namespace URLs.
;;; This is needed for alienate-xml ???
(defn explicit-root-ns
  "Return argument x/element-nss map modified so that that the empty-string namespace is 'root' or whatever
   If the schema uses 'xs' for 'http://www.w3.org/2001/XMLSchema', change it to xsd"
  [nspaces & {:keys [root-name] :or {root-name "ROOT"}}]
  (when (-> nspaces :p->u (contains? root-name))
    (log/warn "XML uses explicit 'root' namespace alias.")) ; POD so pick something else. NYI.
  (as-> nspaces ?ns
    (assoc-in ?ns [:p->u root-name] (or (get (:p->u ?ns) "") :mm/nil))
    (update ?ns :p->u (fn [pu] (as-> pu ?pu
                                   (dissoc ?pu "")
                                   (reduce-kv (fn [m k v]
                                                (if (= v :mm/nil)
                                                  (assoc m k v)
                                                  (assoc m k (-> v url/url-encode))))
                                              {} ?pu))))
    (update ?ns :u->ps
            (fn [uri2alias-map]
              (reduce-kv (fn [res uri aliases]
                           (assoc res (-> uri url/url-encode) (mapv #(if (= % "") root-name %) aliases)))
                         {}
                         uri2alias-map)))
    ;; Now change "xs" to "xsd" if it exists.
    (if (= "http://www.w3.org/2001/XMLSchema" (get (:p->u ?ns) "xs"))
      (as-> ?ns ?ns1
        (assoc-in ?ns1 [:p->u "xsd"] "http://www.w3.org/2001/XMLSchema")
        (update ?ns1 :p->u  #(dissoc % "xs"))
        (update ?ns1 :u->ps #(dissoc % "http://www.w3.org/2001/XMLSchema"))
        (assoc-in ?ns1 [:u->ps "http://www.w3.org/2001/XMLSchema"] ["xsd"]))
      ?ns)))

(defn equivalent-kw [kw u->ps]
  (let [[success? ns-name local-name] (->> kw str (re-matches #"^:xmlns\.(.*)/(.*)$"))]
    (if success?
        (if-let [alias-name (->> ns-name (get u->ps) first)]
          (keyword alias-name  local-name)
          kw)
        kw)))

;;; POD Currently this isn't looking for redefined aliases. It calls x/element-nss just once!
;;; (-> sample-ubl-message io/reader x/parse alienate-xml)
(defn alienate-xml ; Silly, but I like it!
  "Replace namespaced xml map keywords with their aliases."
  [xml u->ps]
  (walk/postwalk
   (fn [obj]
     (if (keyword? obj)
       (equivalent-kw obj u->ps)
       obj))
   xml))

;;; (detagify '{:tag :cbc/InvoiceTypeCode, :attrs {:listID "UN/ECE 1001 Subset", :listAgencyID "6"}, :content ("380")})
(defn detagify
  "Argument in content from clojure.data.xml/parse. Return a map where
    (1) :tag is :schema/type,
    (2) :content, if present, is a simple value or recursively detagified. 
    (3) :attrs, if present, are :xml/attrs.
   The result is that
     (a) returns a string or a map that if it has :xml/content, it is a string or a vector.
     (b) if a map, and the argument had attrs, has an :xml/attrs key."
  [obj]
  (cond (map? obj)
        (as-> obj ?m
          (assoc ?m :xml/tag (:tag ?m))
          (if (not-empty (:attrs   ?m)) (assoc ?m :xml/attrs (:attrs ?m)) ?m)
          (if (not-empty (:content ?m)) (assoc ?m :xml/content (detagify (:content ?m))) ?m)
          (dissoc ?m :tag :attrs :content))
        (seq? obj) (if (and (== (count obj) 1) (-> obj first string?))
                     (first obj)
                     (mapv detagify obj))
        (string? obj) obj ; It looks like nothing will be number? Need schema to fix things. 
        :else (throw (ex-info "Unknown type in detagify" {:obj obj}))))

(defn trans-tag [tag]
  (if-let [ns (namespace tag)]
    (keyword (str ns "_" (name tag)))
    tag))

(defn number-str?
  "This only handles integers and decimals."
  [s]
  (when-let [[_ _sign first-digit decimal?] (re-matches #"^([\+,\-])?(\d)?\d*(\.)?\d*$" s)]
    (or decimal? (not= first-digit "0"))))

(defn simplify-xml
  "Given a map of xml in the form produced by read-xml, change :xml/tag and :xml/content to a map."
  [obj]
  (cond
    (not (or (map? obj) (vector? obj)))
    (if (number-str? obj) (read-string obj) obj)
    (vector? obj) (mapv simplify-xml obj)
    (map? obj) (as-> {} ?r
                 (assoc ?r (trans-tag (:xml/tag obj)) (simplify-xml (:xml/content obj)))
                 (reduce-kv (fn [r key val] (assoc r (trans-tag key) (simplify-xml val)))
                            ?r
                            (:xml/attrs obj)))))

(defn read-xml
  "Return a map of the XML file read."
  [pathname]
  (let [content (-> pathname io/reader x/parse)
        ns-info (explicit-root-ns (x/element-nss content))]
     {:xml/ns-info ns-info
      :xml/content (-> content 
                       (alienate-xml (:u->ps ns-info))
                       clean-whitespace
                       detagify
                       vector)
      :schema/pathname pathname}))

(defn prune-xmi-extensions
  [xml]
  (walk/postwalk
   (fn [obj]
     (if (and (map? obj) (contains? obj :xml/content))
       (update obj :xml/content
               (fn [c] (vec (remove #(and (map? %)
                                          (= (:xml/tag %) :xmi/Extension))
                                    c))))
       obj))
   xml))

(defn xpath-internal
  [content props path-in]
  (loop [result content
         path path-in]
    (cond (empty? path) result,
          (not (map? content)) (when (:warn? props) (log/warn "xpath failed at:" path "in" path-in)),
          :else
          (let [search (first path)]
            (recur
             (if (number? search)
               (nth (:xml/content result) search)
               (some #(when (= search (:xml/tag %)) %) (:xml/content result)))
             (rest path))))))

;;; POD Could enhance this to be REAL XPath. 
(defn xpath
  "Content is a map with :xml/content. Follow the path, each step of
   which selects something from argument's :xml/content
   either an :xml/tag element, in which the first such is chosen, or an index,
   in which case that one is selected."
  [content & path-in]
  (xpath-internal content {:warn? true} path-in))

(defn xpath-
  "Like xpath but without warning on no content."
  [content & path-in]
  (xpath-internal content {} path-in))

;(read-clean "resources/test-files/model3-with-profile.xml")
(defn read-clean [file]
  (as-> (read-xml file) ?x
      (update ?x :xml/content prune-xmi-extensions)
      (dissoc ?x :xml/ns-info)
      (or (xpath ?x :xmi/XMI :uml/Model)       ; M1, typically.
          (xpath ?x :xmi/XMI :uml/Package))))  ; M2, typically. 


(defn parse-xml-string
  "This is useful for debugging. Typical usage:
  (-> sss util/parse-xml-string (xpath :xsd/schema :xsd/complexType) rewrite-xsd)"
  [s]
  (let [pre "<?xml version=\"1.0\" encoding=\"UTF-8\"?>
             <xsd:schema xmlns=\"urn:test-string\"
                         xmlns:xsd=\"http://www.w3.org/2001/XMLSchema\"
                         targetNamespace=\"urn:test-string\"
                         elementFormDefault=\"qualified\"
                         attributeFormDefault=\"unqualified\"
                         version=\"2.3\">"
        post "</xsd:schema>"
        content (x/parse-str (str pre s post))
        ns-info (explicit-root-ns (x/element-nss content))]
    (-> {} ; POD Fix this. Use read-xml, with-out-str, keyword for :reader.
        (assoc :xml/ns-info ns-info)
        (assoc :xml/content (-> content
                                (alienate-xml (:u-ps ns-info))
                                clean-whitespace
                                detagify
                                vector)))))

(defn xpath-internal
  [content props path-in]
  (loop [result content
         path path-in]
    (cond (empty? path) result,
          (not (map? content)) (when (:warn? props) (log/warn "xpath failed at:" path "in" path-in)),
          :else
          (let [search (first path)]
            (recur
             (if (number? search)
               (nth (:xml/content result) search)
               (some #(when (= search (:xml/tag %)) %) (:xml/content result)))
             (rest path))))))

;;; POD Could enhance this to be REAL XPath. 
(defn xpath
  "Content is a map with :xml/content. Follow the path, each step of
   which selects something from argument's :xml/content
   either an :xml/tag element, in which the first such is chosen, or an index,
   in which case that one is "
  [content & path-in]
  (xpath-internal content {:warn? true} path-in))

(defn xpath-
  "Like xpath but without warning on no content."
  [content & path-in]
  (xpath-internal content {} path-in))
             
;;; POD More sophisticated usage???  
(defn xml-type?
  "Return true if the content has :xml/tag = the argument."
  [xml xtype]
  (= (:xml/tag xml) xtype))

(defn nspaces
  "Return a string of n spaces."
  [n]
  (reduce (fn [s _] (str s " ")) "" (range n)))

(defn dir-up
  "file is java.io file. Return the path of the nth parent directory, applied recursively to the ."
  [file n]
  (if (> n 0) 
    (recur (.getParentFile file) (dec n))
    file))

(defn string-permute
  "Return a lazy sequence of the name of columns"
  ([chars] (string-permute [""] chars))
  ([prev chars]
   (let [strs (mapcat (fn [c] (map (fn [s] (str c s)) prev)) chars)]
     (lazy-cat strs (string-permute strs chars)))))
