;;;; package.lisp

(defpackage #:bliss
  (:use #:common-lisp)
  (:export
   ;; lookup
   #:lookup #:english #:aliases #:components #:symbol-p #:word-p
   ;; composition and layout
   #:base-symbols #:layout #:layout-left #:layout-right #:layout-top #:layout-bottom
   #:layout-items #:placed-id #:placed-x #:placed-y
   ;; rendering
   #:svg
   ;; identifiers for programs
   #:bliss-symbol #:bliss-symbol-key #:enable-bliss-syntax #:*bliss-package*
   ;; database statistics
   #:symbol-count #:word-count #:all-symbol-keys #:all-word-keys
   ;; constants
   #:+blissheight+ #:+margin+ #:+radius+ #:+stroke+))

(defpackage #:bliss-words
  (:use)
  (:documentation "Symbols naming Blissymbols words, e.g. bliss-words::|friend|. See BLISS:BLISS-SYMBOL."))

(defpackage #:bliss-tests
  (:use #:common-lisp #:bliss)
  (:export #:run-all))
