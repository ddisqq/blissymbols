;;;; svg.lisp -- port of to_svg_obj: resolve a symbol into drawing primitives and emit SVG.

(in-package #:bliss)

(defun data-kind (key)
  (cond ((gethash key *paths*) :path)
        ((gethash key *shapes*) :shape)
        ((gethash key *chars*) :char)
        ((gethash key *words*) :word)
        (t (error "No drawing data for ~S" key))))

(defun field (alist name) (cdr (assoc name alist :test #'string=)))

(defun emit-primitives (obj x y out)
  "Collect drawing primitives (alists) for OBJ at offset X, Y (data coordinates).
Returns OUT with primitives pushed in drawing order (reverse it at the end)."
  (ecase (data-kind obj)
    (:path
     (let* ((alist (gethash obj *paths*))
            (clone
              (loop for (k . v) in alist
                    collect (cons k
                                  (cond ((not (numberp v)) v)
                                        ((or (string= k "qx") (char= (char k 0) #\x)) (+ v x))
                                        ((or (string= k "qy") (char= (char k 0) #\y))
                                         (- +blissheight+ v y))
                                        (t v))))))
       (let ((form (field clone "form")))
         (cond ((string= form "text")
                (setf clone (acons "x" (+ (field clone "x") (/ (field clone "w") 2)) clone))
                (setf clone (acons "y" (+ (field clone "y") (field clone "h")) clone)))
               ((string= form "dot")
                (setf clone (acons "r" +radius+ clone)))))
       (push clone out)
       out))
    (:shape
     (dolist (item (gethash obj *shapes*) out)
       (destructuring-bind (ref ix iy) item
         (setf out (emit-primitives ref (+ x ix) (+ y iy) out)))))
    ((:char :word)
     (let ((items (if (eq (data-kind obj) :char)
                      (char-def-parts (gethash obj *chars*))
                      (error "Use EXPAND-WORD for word ~S" obj))))
       (dolist (item items out)
         (destructuring-bind (ref ix iy) item
           (setf out (emit-primitives ref (+ x ix) (+ y iy) out))))))))

(defun primitives-of (layout)
  (let ((out '()))
    (dolist (p (layout-items layout) (nreverse out))
      (setf out (emit-primitives (placed-id p) (placed-x p) (placed-y p) out)))))

;;; Number formatting: three decimals, trailing zeros removed (same rule as bliss_core.fmt).

(defun fmt-num (v)
  (let* ((r (/ (round (* (float v 1d0) 1000)) 1000d0))
         (s (format nil "~,3F" r)))
    (when (find #\. s)
      (setf s (string-right-trim "." (string-right-trim "0" s))))
    (if (or (string= s "-0") (string= s "")) "0" s)))

(defun xml-escape (s)
  (with-output-to-string (out)
    (loop for c across s
          do (case c
               (#\< (write-string "&lt;" out))
               (#\> (write-string "&gt;" out))
               (#\& (write-string "&amp;" out))
               (#\" (write-string "&quot;" out))
               (t (write-char c out))))))

(defun svg-element (p)
  (flet ((n (k) (fmt-num (field p k))))
    (let ((form (field p "form")))
      (cond ((string= form "dot")
             (format nil "<circle class=\"bliss-dot\" cx=\"~A\" cy=\"~A\" r=\"~A\"/>" (n "x") (n "y") (n "r")))
            ((string= form "disc")
             (format nil "<circle class=\"bliss-disc\" cx=\"~A\" cy=\"~A\" r=\"~A\"/>" (n "x") (n "y") (n "r")))
            ((string= form "circle")
             (format nil "<circle class=\"bliss-line\" cx=\"~A\" cy=\"~A\" r=\"~A\"/>" (n "x") (n "y") (n "r")))
            ((string= form "text")
             (format nil "<text class=\"bliss-text\" text-anchor=\"middle\" x=\"~A\" y=\"~A\" style=\"font-size:~Apx\">~A</text>"
                     (n "x") (n "y") (fmt-num (field p "fontsize")) (xml-escape (field p "text"))))
            ((string= form "line")
             (format nil "<line class=\"bliss-line\" x1=\"~A\" y1=\"~A\" x2=\"~A\" y2=\"~A\"/>"
                     (n "x1") (n "y1") (n "x2") (n "y2")))
            ((string= form "arc")
             (format nil "<path class=\"bliss-line\" d=\"M ~A,~A A ~A,~A 0 0,0 ~A,~A\"/>"
                     (n "x1") (n "y1") (n "rx") (n "ry") (n "x2") (n "y2")))
            ((string= form "bigarc")
             (format nil "<path class=\"bliss-line\" d=\"M ~A,~A A ~A,~A 0 1,0 ~A,~A\"/>"
                     (n "x1") (n "y1") (n "rx") (n "ry") (n "x2") (n "y2")))
            ((string= form "quadratic")
             (format nil "<path class=\"bliss-line\" d=\"M ~A,~A Q ~A,~A ~A,~A\"/>"
                     (n "x1") (n "y1") (n "qx") (n "qy") (n "x2") (n "y2")))
            (t (error "Unknown drawing form ~S" form))))))

(defparameter *svg-style*
  ".bliss-line,.bliss-disc,.bliss-dot{stroke:#000;stroke-width:8;stroke-linejoin:round;stroke-linecap:round}.bliss-line{fill:none}.bliss-disc,.bliss-dot{fill:#000}.bliss-text{font-family:'Helvetica Neue',Helvetica,Arial,'Liberation Sans',sans-serif}")

(defun svg-string (word &key title)
  "Standalone SVG for a word (a key or a list of keys), with the viewer's margins."
  (let* ((lay (layout word))
         (m +margin+)
         (x0 (- (layout-left lay) m))
         (y0 (- (layout-top lay) m))
         (w (+ (- (layout-right lay) (layout-left lay)) (* 2 m)))
         (h (+ (- (layout-bottom lay) (layout-top lay)) (* 2 m))))
    (with-output-to-string (s)
      (format s "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"~A ~A ~A ~A\" width=\"~A\" height=\"~A\">"
              (fmt-num x0) (fmt-num y0) (fmt-num w) (fmt-num h) (fmt-num w) (fmt-num h))
      (when title (format s "<title>~A</title>" (xml-escape title)))
      (format s "<style>~A</style><g>" *svg-style*)
      (dolist (p (primitives-of lay))
        (write-string (svg-element p) s))
      (write-string "</g></svg>" s))))
