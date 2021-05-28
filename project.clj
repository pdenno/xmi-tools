(defproject pdenno/xmi_tools "0.1.64"
  :description "A library for parsing and analyzing XMI"
  :url "http://github/pdenno/xmi-tools"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure     "1.10.3"]
                 [metosin/malli           "0.5.1"]
                 [com.taoensso/timbre     "5.1.2"]]
  :source-paths ["src/main"]
  :repl-options {:init-ns pdenno.xmi.xmi})
