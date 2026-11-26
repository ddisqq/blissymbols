;;;; run.lisp -- sbcl --script tests/run.lisp
(load (merge-pathnames "../bliss.lisp" *load-truename*))
(load (merge-pathnames "fixtures.lisp" *load-truename*))
(load (merge-pathnames "tests.lisp" *load-truename*))
(unless (bliss-tests:run-all) (sb-ext:exit :code 1))
