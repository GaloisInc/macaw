; The identity function for a Byte
(defun @byte_id ((x Byte)) Byte
  (start start:
    (return x)))

(defun @test_byte_id () Unit
  (start start:
    (let input (fresh Byte))
    (let input_back (funcall @byte_id input))
    (assert! (equal? input input_back) "byte_id test")
    (return ())))