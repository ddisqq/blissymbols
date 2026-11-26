;;;; layout.lisp -- port of expand_word / expand_list / spacing / kerning from blissviewer.ts.

(in-package #:bliss)

(defconstant +qspace+ 32d0 "BLISSQSPACE = BLISSQUARE / 4 with BLISSQUARE = 128.")

(defparameter *modifiers*
  (let ((h (make-hash-table :test 'equal)))
    (dolist (m '("a,an,any" "ago,then_(past)" "belongs_to,of_(possessive)" "bliss-name"
                 "comparative_more" "dot" "generalization" "group_of,much_of,many_of,quantity_of"
                 "combine_marker" "intensity" "line,stripe" "metaphor" "minus,no,without" "more"
                 "most,maximum" "now" "opposite_meaning,opposite_of,opposite"
                 "part,bit,piece,portion,part_of" "superlative_most" "then,so,later")
             h)
      (setf (gethash m h) t))))

(defparameter *punctuations*
  (let ((h (make-hash-table :test 'equal)))
    (dolist (p '("comma" "period,point,full_stop,decimal_point" "question_mark" "exclamation_mark") h)
      (setf (gethash p h) t))))

(defun ends-with (suffix s)
  (and (>= (length s) (length suffix))
       (string= suffix s :start2 (- (length s) (length suffix)))))

(defun modifier-p (s) (gethash s *modifiers*))
(defun punctuation-p (s) (gethash s *punctuations*))
(defun digit-p (s) (ends-with "(digit)" s))
(defun letter-p (s) (or (ends-with "(uppercase)" s) (ends-with "(lowercase)" s)))
(defun indicator-p (s)
  (and (>= (length s) 10) (string= "indicator_" s :end2 10) (not (modifier-p s))))

(defun char-width (key)
  (let ((c (gethash key *chars*)))
    (unless c (error "Unknown symbol ~S" key))
    (or (char-def-width c) 0d0)))

(defun char-height (key)
  (let ((c (gethash key *chars*)))
    (unless c (error "Unknown symbol ~S" key))
    (or (char-def-height c) 0d0)))

(defun default-kerning (h)
  (cond ((or (null h) (zerop h)) 12)
        ((<= h 80) 2)
        ((<= h 144) 6)
        (t 14)))

(defun kerning-possible-p (prev cur)
  (when (or (<= (char-width prev) 24d0) (<= (char-width cur) 24d0))
    (return-from kerning-possible-p nil))
  (let* ((r (gethash prev *kerning-right*))
         (r (if (and r (/= r 0)) r (default-kerning (char-height prev))))
         (l (gethash cur *kerning-left*))
         (l (if (and l (/= l 0)) l (default-kerning (char-height cur)))))
    (zerop (logand r l))))

(defun spacing (prev cur)
  (cond ((null prev) 0d0)
        ((kerning-possible-p prev cur) 0d0)
        ((and (digit-p prev) (digit-p cur)) (/ +qspace+ 2))
        ((and (letter-p prev) (letter-p cur)) (/ +qspace+ 2))
        ((string= cur "comma") (* +qspace+ 3/4))
        (t +qspace+)))

(defstruct grp ch inds)

(defun expand-list (words inds)
  "Returns (values groups leftover-indicators), as in expand_list()."
  (let ((chars (make-array 0 :adjustable t :fill-pointer t)))
    (loop for w in words
          for n from 0
          do (cond ((and (indicator-p w) (> (length chars) 0))
                    (let ((last (aref chars (1- (length chars)))))
                      (setf (grp-inds last) (append (grp-inds last) inds (list w))))
                    (setf inds '()))
                   ((or (modifier-p w) (punctuation-p w) (and (= n 0) (digit-p w)))
                    (vector-push-extend (make-grp :ch w :inds '()) chars))
                   (t
                    (vector-push-extend (make-grp :ch w :inds inds) chars)
                    (setf inds '()))))
    (let ((groups '()) (new-inds '()))
      (loop for c across chars
            do (let ((ch (grp-ch c)) (cinds (grp-inds c)))
                 (cond ((gethash ch *words*)
                        (multiple-value-bind (sub-groups sub-left)
                            (expand-list (gethash ch *words*) (append new-inds cinds))
                          (setf groups (append groups sub-groups))
                          (setf new-inds sub-left)))
                       (t
                        (unless (gethash ch *chars*)
                          (warn "Unknown character ~S; using question_mark" ch)
                          (setf ch "question_mark"))
                        (setf groups (append groups (list (make-grp :ch ch :inds (append new-inds cinds)))))
                        (setf new-inds '())))))
      (values groups (append new-inds inds)))))

(defstruct placed id x y)

(defstruct layout
  (left 0d0) (right 0d0) (top 0d0) (bottom +blissheight+) (items '()))

(defun expand-word (word)
  "Lay out a Blisswords word: a key or a list of keys. Returns a LAYOUT."
  (let ((words (if (listp word) word (list word))))
    (multiple-value-bind (groups leftover) (expand-list words '())
      (when leftover
        (warn "Indicators left over: ~S" leftover))
      (let ((items '()) (x 0d0) (left 0d0) (right 0d0) (prev nil))
        (dolist (g groups)
          (let* ((ch (grp-ch g)) (inds (grp-inds g))
                 (w (char-width ch)))
            (incf x (spacing prev ch))
            (push (make-placed :id ch :x x :y 0d0) items)
            (when inds
              (let* ((iw (* (/ (1- (length inds)) 2) +qspace+)))
                (dolist (ind inds)
                  (incf iw (char-width ind))
                  (let ((c (gethash ind *center*))) (when c (incf iw (* 2 c)))))
                (let ((ix (+ x (/ (- w iw) 2)))
                      (iy (max 0d0 (- (char-height ch) 192d0))))
                  (let ((c (gethash ch *center*))) (when c (incf ix c)))
                  (setf left (min left ix))
                  (loop for ind in inds
                        for i from 0
                        do (when (> i 0) (incf ix (/ +qspace+ 2)))
                           (push (make-placed :id ind :x ix :y iy) items)
                           (incf ix (char-width ind)))
                  (setf right (max right ix)))))
            (incf x w)
            (setf prev ch)))
        (setf right (max right x))
        (make-layout :left left :right right :top 0d0 :bottom +blissheight+
                     :items (reverse items))))))

(defun layout (word)
  "Public entry point: positioned symbols and bounds for a word (a key or list of keys)."
  (expand-word word))

(defun base-symbols (word)
  "The symbols a word is made of, flattened, in writing order (indicators included)."
  (mapcar #'placed-id (layout-items (layout word))))
