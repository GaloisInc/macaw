(defun @byte_id ((x (Bitvector 8))) (Bitvector 8)
  (start start:
    (return x)))

(defun @main () Unit
  (start start:
    (let input (fresh (Bitvector 8)))
    (let input_back (funcall @byte_id input))
    (assert! (equal? input input_back) "byte_id test")
    (return ())))