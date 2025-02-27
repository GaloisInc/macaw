; A function that demonstrates the use of all of the operations
(defun @ops ((p Pointer) (q Pointer)) Unit
  (start start:
    (let b (bv-typed-literal SizeT 42))
    (let bp (bits-to-pointer b))
    (let pb (pointer-to-bits bp))
    (let n (pointer-make-null))
    (let d (pointer-diff p q))
    (let r (pointer-add p d))
	(let s (pointer-sub r d))
	(let e (pointer-eq s p))
    (let t (pointer-read Int le s))
    (pointer-write SizeT le s b)
    (return ())))
