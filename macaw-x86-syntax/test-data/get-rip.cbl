(defun @id ((regs X86Regs)) (Ptr 64)
  (start start:
    (let b (get-reg rip regs))
    (return b)))