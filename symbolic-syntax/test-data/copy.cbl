; A basic function that copies the data pointed to by one pointer to another
(defun @copy ((src Pointer) (dest Pointer)) Unit
  (start start:
    (let src-data (pointer-read Int le src))
    (pointer-write Int le dest src-data)
    (return ())))