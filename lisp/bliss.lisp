;;;; bliss.lisp -- convenience loader: (load "lisp/bliss.lisp") loads the system without ASDF.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (let ((here (make-pathname :name nil :type nil :defaults (or *load-truename* *default-pathname-defaults*))))
    (dolist (f '("src/package" "src/data" "src/tables" "src/layout" "src/svg" "src/api"))
      (load (merge-pathnames (concatenate 'string f ".lisp") here)))))
