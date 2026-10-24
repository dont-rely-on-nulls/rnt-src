;; Tuples of an RNT relation, as Translator.ml writes and reads them: a
;; tuple is #(Type #m(Name Value ...)), its type, names and strings
;; binaries, and its integers no wider than an OCaml int.
(defmodule rnt
  (export (recv 1) (send 1)))

;; A tuple from the bytes RNT sent.
(defun recv (bytes) (holdable (binary_to_term bytes '(safe))))

;; The bytes RNT reads a tuple from.
(defun send (tuple) (term_to_binary (holdable tuple)))

;; The tuple, if RNT can hold it.
(defun holdable
  (((= (tuple type attributes) tuple)) (when (is_binary type) (is_map attributes))
   (if (lists:all (fun attribute? 1) (maps:to_list attributes))
     tuple
     (error 'badarg (list tuple))))
  ((tuple) (error 'badarg (list tuple))))

(defun attribute?
  (((tuple name value)) (when (is_binary name) (is_binary value)) 'true)
  (((tuple name value))
   (when (is_binary name) (is_integer value) (>= value (- (bsl 1 62))) (< value (bsl 1 62)))
   'true)
  ((_) 'false))
