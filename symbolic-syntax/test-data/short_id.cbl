; The identity function for a 16-bit int
(defun @short_id ((x Short)) Short
  (start start:
    (return x)))

(defun @test_short_id () Unit
  (start start:
    (let input (fresh Short))
    (let input_back (funcall @short_id input))
    (assert! (equal? input input_back) "short_id test")
    (return ())))