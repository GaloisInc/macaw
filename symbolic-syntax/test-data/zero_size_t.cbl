; A basic function that returns a size_t containing zero
(defun @zero_size_t () SizeT
  (start start:
    (let zero (bv-typed-literal SizeT 0))
    (return zero)))