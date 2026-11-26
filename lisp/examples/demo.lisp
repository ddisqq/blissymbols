;;;; demo.lisp -- a short tour of the bliss library.
;;;; Run from the lisp/ directory:  sbcl --script examples/demo.lisp
(require :asdf)
(push (truename "./") asdf:*central-registry*)
(asdf:load-system "bliss")
(in-package #:bliss)

(format t "~&Symbols: ~D, words: ~D~%" (symbol-count) (word-count))

;; English names resolve to database keys
(format t "~&\"sun\"    -> ~S~%" (lookup "sun"))
(format t "~&\"friend\" -> ~S (components ~S)~%" (lookup "friend") (components (lookup "friend")))

;; Composition: the symbols a word is written with, in order
(format t "~&base symbols of \"friend\": ~{~A~^, ~}~%" (base-symbols "friend"))

;; Layout: positions of every symbol, in Blissymbol units (a square is 128)
(let ((lay (layout "friend")))
  (format t "~&layout width ~A, ~D placed symbols~%"
          (- (layout-right lay) (layout-left lay)) (length (layout-items lay))))

;; Programs can use Blisswords as symbols
(enable-bliss-syntax)
(defun mood-colour (word)
  (case word
    (#@"happy" :yellow)
    (#@"sad" :blue)
    (t :grey)))
(format t "~&mood-colour of happy: ~S, of sad: ~S~%" (mood-colour '#@"happy") (mood-colour '#@"sad"))
(format t "~&symbol ~S maps back to ~S~%" '#@"friend" (bliss-symbol-key '#@"friend"))

;; Write an SVG drawing
(with-open-file (out "friend.svg" :direction :output :if-exists :supersede)
  (write-string (svg "friend" :title "friend") out))
(format t "~&wrote friend.svg~%")
