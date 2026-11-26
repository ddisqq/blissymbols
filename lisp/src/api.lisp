;;;; api.lisp -- the public interface of the bliss library.

(in-package #:bliss)

(defun normalize-name (name)
  "Accept \"on board\" as well as \"on_board\"."
  (substitute #\_ #\Space name))

(defun first-match (table name)
  "Shortest matching key in a name index, or NIL."
  (let ((keys (gethash (string-downcase name) table)))
    (when keys
      (first (sort (copy-list keys) #'< :key #'length)))))

(defun lookup (name)
  "Resolve an English name to its database key (a string), or NIL.
Symbols are preferred over composed words with the same name."
  (let ((n (normalize-name name)))
    (or (and (or (gethash n *chars*) (gethash n *words*)) n)
        (first-match *name-index* n)
        (first-match *alias-index* n))))

(defun english (key)
  "The English names of a database key, underscores turned into spaces, first name first."
  (mapcar (lambda (n) (substitute #\Space #\_ n)) (split-names key)))

(defun aliases (key)
  "The other English names of a key (english minus the first)."
  (rest (english key)))

(defun components (key)
  "The direct components of a composed word, as database keys (NIL for a symbol)."
  (gethash key *words*))

(defun base-symbols-of (name)
  "Like BASE-SYMBOLS but takes an English name and resolves it first."
  (let ((key (lookup name)))
    (unless key (error "Unknown Blissymbol ~S" name))
    (base-symbols key)))

(defun svg (word &key title)
  "Standalone SVG text for a name, key or list of keys."
  (svg-string (if (stringp word) (or (lookup word) (error "Unknown Blissymbol ~S" word)) word)
              :title title))

;;; Identifiers for programs

(defun bliss-symbol (name)
  "The Lisp symbol for a Blisswords word, e.g. (bliss-symbol \"friend\") => BLISS-WORDS::|friend|.
Signals an error for unknown names."
  (let ((key (lookup name)))
    (unless key (error "Unknown Blissymbol ~S" name))
    (let* ((headword (first (split-names key)))
           (sym (intern headword *bliss-package*)))
      (setf (gethash sym *symbol-keys*) key)
      sym)))

(defun bliss-symbol-key (sym)
  "The database key for a symbol made by BLISS-SYMBOL, or NIL."
  (gethash sym *symbol-keys*))

(defun read-bliss-word (stream subchar arg)
  "Reader macro function for #@\"name\"."
  (declare (ignore subchar arg))
  (let ((name (read stream t nil t)))
    (unless (stringp name)
      (error "#@ expects a string, e.g. #@\"friend\", not ~S" name))
    (bliss-symbol name)))

(defun enable-bliss-syntax (&optional (readtable *readtable*))
  "Make #@\"name\" read as the Lisp symbol for a Blisswords word in READTABLE (default: the current one)."
  (set-dispatch-macro-character #\# #\@ #'read-bliss-word readtable)
  readtable)
