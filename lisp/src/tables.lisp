;;;; tables.lisp -- turn the generated raw data into hash tables and name indexes.

(in-package #:bliss)

(defconstant +blissheight+ 320d0 "Data coordinates are flipped about this height (blissviewer.ts).")
(defconstant +margin+ 8d0 "Default margin around a drawing (blissviewer.ts).")
(defconstant +radius+ 4d0 "Dot radius used by blissdemo.js.")
(defconstant +stroke+ 8d0 "Stroke width from blissviewer.css.")

(defvar *bliss-package* (find-package '#:bliss-words)
  "Package that holds one symbol per Blisswords word created by BLISS-SYMBOL.")

(defstruct (char-def (:constructor make-char-def (name width height parts)))
  name width height parts)

(defvar *chars* (make-hash-table :test 'equal) "key -> char-def")
(defvar *paths* (make-hash-table :test 'equal) "key -> alist of fields")
(defvar *shapes* (make-hash-table :test 'equal) "key -> list of (ref x y)")
(defvar *words* (make-hash-table :test 'equal) "key -> list of component keys")
(defvar *center* (make-hash-table :test 'equal))
(defvar *kerning-left* (make-hash-table :test 'equal))
(defvar *kerning-right* (make-hash-table :test 'equal))

(defvar *name-index* (make-hash-table :test 'equal)
  "lowercase first name -> keys (characters first, then words)")
(defvar *alias-index* (make-hash-table :test 'equal)
  "lowercase any name -> keys (characters first, then words)")
(defvar *symbol-keys* (make-hash-table :test 'eq)
  "symbol in BLISS-WORDS -> database key")

(defun split-names (key)
  "\"a,b,c\" -> (\"a\" \"b\" \"c\")"
  (let ((out '()) (start 0))
    (loop for i from 0 to (length key)
          do (when (or (= i (length key)) (char= (char key i) #\,))
               (when (> i start) (push (subseq key start i) out))
               (setf start (1+ i))))
    (nreverse out)))

(defun index-key (table name key)
  (let ((k (string-downcase name)))
    (setf (gethash k table) (append (gethash k table) (list key)))))

(defun build-tables ()
  (clrhash *chars*) (clrhash *paths*) (clrhash *shapes*) (clrhash *words*)
  (clrhash *center*) (clrhash *kerning-left*) (clrhash *kerning-right*)
  (clrhash *name-index*) (clrhash *alias-index*) (clrhash *symbol-keys*)
  (dolist (c *raw-chars*)
    (destructuring-bind (key w h parts) c
      (setf (gethash key *chars*)
            (make-char-def key (float w 1d0) (and h (float h 1d0))
                           (mapcar (lambda (p) (list (first p) (float (second p) 1d0) (float (third p) 1d0)))
                                   parts)))))
  (dolist (c *raw-center*) (setf (gethash (car c) *center*) (float (cdr c) 1d0)))
  (dolist (c *raw-kerning-left*) (setf (gethash (car c) *kerning-left*) (cdr c)))
  (dolist (c *raw-kerning-right*) (setf (gethash (car c) *kerning-right*) (cdr c)))
  (dolist (p *raw-paths*) (setf (gethash (car p) *paths*) (cdr p)))
  (dolist (s *raw-shapes*)
    (setf (gethash (car s) *shapes*)
          (mapcar (lambda (p) (list (first p) (float (second p) 1d0) (float (third p) 1d0))) (cdr s))))
  (dolist (w *raw-words*) (setf (gethash (car w) *words*) (cdr w)))
  ;; name indexes: characters first, then words, so that a symbol wins over a composed word
  (dolist (src (list (loop for k being the hash-keys of *chars* collect k)
                     (loop for k being the hash-keys of *words* collect k)))
    (dolist (key (sort (copy-list src) #'string<))
      (let ((names (split-names key)))
        (when names
          (index-key *name-index* (first names) key))
        (dolist (n names) (index-key *alias-index* n key)))))
  (values))

(build-tables)

(defun symbol-p (key) (and (gethash key *chars*) t))
(defun word-p (key) (and (gethash key *words*) t))
(defun symbol-count () (hash-table-count *chars*))
(defun word-count () (hash-table-count *words*))
(defun all-symbol-keys () (sort (loop for k being the hash-keys of *chars* collect k) #'string<))
(defun all-word-keys () (sort (loop for k being the hash-keys of *words* collect k) #'string<))
