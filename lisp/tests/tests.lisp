;;;; tests.lisp -- tests for the bliss library. Run with: sbcl --script tests/run.lisp

(in-package #:bliss-tests)

;; the file uses #@"name" literals below, so install the reader syntax while reading it
(eval-when (:compile-toplevel :load-toplevel :execute)
  (bliss:enable-bliss-syntax))

(defvar *failures* 0)
(defvar *passes* 0)

(defmacro check (form &optional (label (prin1-to-string form)))
  `(if ,form
       (incf *passes*)
       (progn (incf *failures*)
              (format t "~&FAIL: ~A~%" ,label))))

(defun close-enough (a b) (< (abs (- a b)) 1d-9))

(defun test-layouts ()
  (dolist (exp bliss::*expected-layouts*)
    (destructuring-bind (key left right items) exp
      (let ((lay (layout key)))
        (check (close-enough (layout-left lay) left) (format nil "~A left" key))
        (check (close-enough (layout-right lay) right) (format nil "~A right" key))
        (check (= (length (layout-items lay)) (length items)) (format nil "~A item count" key))
        (loop for p in (layout-items lay)
              for (id x y) in items
              do (check (and (string= (placed-id p) id)
                             (close-enough (placed-x p) x)
                             (close-enough (placed-y p) y))
                        (format nil "~A item ~A" key id)))))))

(defun test-lookup ()
  (check (string= (lookup "friend") "friend"))
  (check (string= (lookup "on board") "aboard,on_board") "alias with a space")
  (check (null (lookup "no-such-word-xyz")))
  (check (equal (english "ability_(half_sized)") '("ability (half sized)")))
  (check (equal (aliases "aboard,on_board") '("on board")))
  (check (components "friend") "components of a word")
  (check (null (components "sun")) "a symbol has no components")
  (check (symbol-p "sun") "symbol-p")
  (check (word-p "friend") "word-p")
  (check (= (symbol-count) 1150) "1150 symbols")
  (check (= (word-count) 4675) "4675 words"))

(defun test-symbols-for-programs ()
  (let ((s (bliss-symbol "friend")))
    (check (eq (symbol-package s) (find-package '#:bliss-words)) "symbol lives in BLISS-WORDS")
    (check (string= (symbol-name s) "friend") "symbol name is the headword")
    (check (eq s (bliss-symbol "friend")) "same name gives the same symbol")
    (check (string= (bliss-symbol-key s) "friend") "symbol maps back to its key"))
  (check (handler-case (progn (bliss-symbol "no-such-word-xyz") nil)
           (error () t))
         "unknown names signal an error")
  ;; reader syntax: #@"name" reads as the symbol, usable in CASE and as data
  (let ((*readtable* (copy-readtable nil)))
    (enable-bliss-syntax)
    (check (eq (read-from-string "#@\"friend\"") (bliss-symbol "friend")) "#@ reader macro")
    (let ((mood (read-from-string "#@\"happy\"")))
      (check (eq (case mood
                   (#@"sad" :low)
                   (#@"happy" :high)
                   (t :unknown))
                 :high)
             "symbols as CASE keys"))))

(defun count-substring (needle hay)
  (loop with start = 0
        for pos = (search needle hay :start2 start)
        while pos
        count t
        do (setf start (+ pos (length needle)))))

(defun test-svg ()
  (let ((s (svg "friend")))
    (check (search "<svg " s) "svg root")
    (check (search "</svg>" s) "svg closes")
    (check (= (count-substring "class=\"bliss-" s)
              (length (bliss::primitives-of (layout "friend"))))
           "one SVG element per drawing primitive")
    (check (search "viewBox=\"-8 -8 " s) "viewBox includes the margin"))
  (check (search "<title>a</title>" (svg "a" :title "a")) "title is escaped and included")
  (check (string= (bliss::fmt-num 0.5d0) "0.5") "fmt-num drops trailing zeros")
  (check (string= (bliss::fmt-num 12d0) "12") "fmt-num integers")
  (check (string= (bliss::fmt-num -16d0) "-16") "fmt-num negatives")
  (check (string= (bliss::fmt-num -0.0001d0) "0") "fmt-num avoids -0"))

(defun run-all ()
  (setf *failures* 0 *passes* 0)
  (test-layouts)
  (test-lookup)
  (test-symbols-for-programs)
  (test-svg)
  (format t "~&~D passed, ~D failed~%" *passes* *failures*)
  (zerop *failures*))
