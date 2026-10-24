;; The node of the beam evaluator, which Beam.ml starts and speaks to
;; over stdin and stdout, with the messages Beam.ml lists. A program is
;; a function taking one relation per input and giving back a relation:
;; a function from a limit to at most that many tuples and the rest of
;; the relation, or done when there are no more. Its tuples are as
;; rnt:recv/1 gives and rnt:send/1 takes them.
(defmodule rnt-node
  (export (start 0)))

(defun start ()
  ;; The default handler prints to stdout, where it would break a frame.
  (logger:remove_handler 'default)
  (logger:add_handler 'default 'logger_std_h (map 'config (map 'type 'standard_error)))
  (put 'port (open_port #(fd 0 1) '(binary #(packet 4) eof)))
  (loop))

(defun loop () (serve (read-frame)) (loop))

(defun read-frame ()
  (let ((port (get 'port)))
    (receive
      ((tuple p (tuple 'data frame)) (when (=:= p port)) frame)
      ((tuple p 'eof) (when (=:= p port)) (halt)))))

(defun write-frame (message) (port_command (get 'port) message))

;; A function that cannot be applied leaves a relation that fails when read.
(defun serve
  (((binary #\i (cursor (size 32)) (m (size 16)) (module binary (size m))
            (f (size 16)) (func binary (size f)) (readers binary)))
   (put (tuple 'cursor cursor)
        (try
          (apply (binary_to_existing_atom module) (binary_to_existing_atom func)
                 (lc ((<= (binary (reader (size 32))) readers)) (relation reader)))
          (catch
            ((tuple class reason stack) (lambda (_) (erlang:raise class reason stack)))))))
  (((binary #\f (cursor (size 32)) (limit (size 32))))
   (write-frame
     (try (fetch cursor limit)
       (catch
         ((tuple class reason _) (list #\e (io_lib:format "~p:~p" (list class reason))))))))
  (((binary #\c (cursor (size 32))))
   (erase (tuple 'cursor cursor))))

(defun fetch (cursor limit)
  (case (get (tuple 'cursor cursor))
    ('done (batch '() 'true))
    (relation
     (let (((tuple tuples rest) (funcall relation limit)))
       (put (tuple 'cursor cursor) rest)
       (batch tuples (=:= rest 'done))))))

(defun batch (tuples exhausted)
  (list* #\b (if exhausted 1 0)
         (lc ((<- tuple tuples))
           (let ((term (rnt:send tuple)))
             (list (binary ((byte_size term) (size 32))) term)))))

;; An input, read through RNT. Reading it moves the reader on, so it can
;; be read once.
(defun relation (reader)
  (lambda (limit)
    (write-frame (binary #\n (reader (size 32)) (limit (size 32))))
    (let (((tuple tuples exhausted) (answer)))
      (tuple tuples (if exhausted 'done (relation reader))))))

;; The answer to a next, serving the calls that come before it.
(defun answer ()
  (case (read-frame)
    ((binary #\b exhausted (tuples binary))
     (tuple (lc ((<= (binary (n (size 32)) (term binary (size n))) tuples)) (rnt:recv term))
            (=:= exhausted 1)))
    ((binary #\e (message binary)) (error (tuple 'rnt message)))
    (call (serve call) (answer))))
