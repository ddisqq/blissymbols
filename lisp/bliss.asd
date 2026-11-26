;;;; bliss.asd -- ASDF system definition for the Blissymbols library.
;;;; Load with: (asdf:load-system "bliss")   (ASDF must be able to find this directory,
;;;; e.g. (push #p"/path/to/blissymbols/lisp/" asdf:*central-registry*)).

(defsystem "bliss"
  :description "Blissymbols for Common Lisp: symbol lookup, composition, layout, SVG and
reader syntax (#@\"word\") so Bliss words can be used as identifiers in code."
  :version "1.0.0"
  :license "See LICENSE in the repository root"
  :serial t
  :components ((:file "src/package")
               (:file "src/data")
               (:file "src/tables")
               (:file "src/layout")
               (:file "src/svg")
               (:file "src/api")))

(defsystem "bliss/tests"
  :description "Tests for the bliss library."
  :depends-on ("bliss")
  :serial t
  :components ((:file "tests/fixtures")
               (:file "tests/tests"))
  :perform (test-op (o c) (uiop:symbol-call :bliss-tests :run-all)))
