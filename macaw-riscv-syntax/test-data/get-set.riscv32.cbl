(defun @id ((regs RISCV32Regs)) RISCV32Regs
  (start start:
    (let pc (get-reg pc regs))
    (let ra (get-reg ra regs))
    (let sp (get-reg sp regs))
    (let gp (get-reg gp regs))
    (let tp (get-reg tp regs))
    (let t0 (get-reg t0 regs))
    (let t1 (get-reg t1 regs))
    (let t2 (get-reg t2 regs))
    (let s0 (get-reg s0 regs))
    (let s1 (get-reg s1 regs))
    (let a0 (get-reg a0 regs))
    (let a1 (get-reg a1 regs))
    (let a2 (get-reg a2 regs))
    (let a3 (get-reg a3 regs))
    (let a4 (get-reg a4 regs))
    (let a5 (get-reg a5 regs))
    (let a6 (get-reg a6 regs))
    (let a7 (get-reg a7 regs))
    (let s2 (get-reg s2 regs))
    (let s3 (get-reg s3 regs))
    (let s4 (get-reg s4 regs))
    (let s5 (get-reg s5 regs))
    (let s6 (get-reg s6 regs))
    (let s7 (get-reg s7 regs))
    (let s8 (get-reg s8 regs))
    (let s9 (get-reg s9 regs))
    (let s10 (get-reg s10 regs))
    (let s11 (get-reg s11 regs))
    (let t3 (get-reg t3 regs))
    (let t4 (get-reg t4 regs))
    (let t5 (get-reg t5 regs))
    (let t6 (get-reg t6 regs))
    (let x1 (get-reg x1 regs))
    (let x2 (get-reg x2 regs))
    (let x3 (get-reg x3 regs))
    (let x4 (get-reg x4 regs))
    (let x5 (get-reg x5 regs))
    (let x6 (get-reg x6 regs))
    (let x7 (get-reg x7 regs))
    (let x8 (get-reg x8 regs))
    (let x9 (get-reg x9 regs))
    (let x10 (get-reg x10 regs))
    (let x11 (get-reg x11 regs))
    (let x12 (get-reg x12 regs))
    (let x13 (get-reg x13 regs))
    (let x14 (get-reg x14 regs))
    (let x15 (get-reg x15 regs))
    (let x16 (get-reg x16 regs))
    (let x17 (get-reg x17 regs))
    (let x18 (get-reg x18 regs))
    (let x19 (get-reg x19 regs))
    (let x20 (get-reg x20 regs))
    (let x21 (get-reg x21 regs))
    (let x22 (get-reg x22 regs))
    (let x23 (get-reg x23 regs))
    (let x24 (get-reg x24 regs))
    (let x25 (get-reg x25 regs))
    (let x26 (get-reg x26 regs))
    (let x27 (get-reg x27 regs))
    (let x28 (get-reg x28 regs))
    (let x29 (get-reg x29 regs))
    (let x30 (get-reg x30 regs))
    (let x31 (get-reg x31 regs))
    (let ft0 (get-reg ft0 regs))
    (let ft1 (get-reg ft1 regs))
    (let ft2 (get-reg ft2 regs))
    (let ft3 (get-reg ft3 regs))
    (let ft4 (get-reg ft4 regs))
    (let ft5 (get-reg ft5 regs))
    (let ft6 (get-reg ft6 regs))
    (let ft7 (get-reg ft7 regs))
    (let fs0 (get-reg fs0 regs))
    (let fs1 (get-reg fs1 regs))
    (let fa0 (get-reg fa0 regs))
    (let fa1 (get-reg fa1 regs))
    (let fa2 (get-reg fa2 regs))
    (let fa3 (get-reg fa3 regs))
    (let fa4 (get-reg fa4 regs))
    (let fa5 (get-reg fa5 regs))
    (let fa6 (get-reg fa6 regs))
    (let fa7 (get-reg fa7 regs))
    (let fs2 (get-reg fs2 regs))
    (let fs3 (get-reg fs3 regs))
    (let fs4 (get-reg fs4 regs))
    (let fs5 (get-reg fs5 regs))
    (let fs6 (get-reg fs6 regs))
    (let fs7 (get-reg fs7 regs))
    (let fs8 (get-reg fs8 regs))
    (let fs9 (get-reg fs9 regs))
    (let fs10 (get-reg fs10 regs))
    (let fs11 (get-reg fs11 regs))
    (let ft8 (get-reg ft8 regs))
    (let ft9 (get-reg ft9 regs))
    (let ft10 (get-reg ft10 regs))
    (let ft11 (get-reg ft11 regs))
    (let f0 (get-reg f0 regs))
    (let f1 (get-reg f1 regs))
    (let f2 (get-reg f2 regs))
    (let f3 (get-reg f3 regs))
    (let f4 (get-reg f4 regs))
    (let f5 (get-reg f5 regs))
    (let f6 (get-reg f6 regs))
    (let f7 (get-reg f7 regs))
    (let f8 (get-reg f8 regs))
    (let f9 (get-reg f9 regs))
    (let f10 (get-reg f10 regs))
    (let f11 (get-reg f11 regs))
    (let f12 (get-reg f12 regs))
    (let f13 (get-reg f13 regs))
    (let f14 (get-reg f14 regs))
    (let f15 (get-reg f15 regs))
    (let f16 (get-reg f16 regs))
    (let f17 (get-reg f17 regs))
    (let f18 (get-reg f18 regs))
    (let f19 (get-reg f19 regs))
    (let f20 (get-reg f20 regs))
    (let f21 (get-reg f21 regs))
    (let f22 (get-reg f22 regs))
    (let f23 (get-reg f23 regs))
    (let f24 (get-reg f24 regs))
    (let f25 (get-reg f25 regs))
    (let f26 (get-reg f26 regs))
    (let f27 (get-reg f27 regs))
    (let f28 (get-reg f28 regs))
    (let f29 (get-reg f29 regs))
    (let f30 (get-reg f30 regs))
    (let f31 (get-reg f31 regs))
    (let mvendorid (get-reg mvendorid regs))
    (let marchid (get-reg marchid regs))
    (let mimpid (get-reg mimpid regs))
    (let mhartid (get-reg mhartid regs))
    (let mstatus (get-reg mstatus regs))
    (let misa (get-reg misa regs))
    (let medeleg (get-reg medeleg regs))
    (let mideleg (get-reg mideleg regs))
    (let mie (get-reg mie regs))
    (let mtvec (get-reg mtvec regs))
    (let mcounteren (get-reg mcounteren regs))
    (let mscratch (get-reg mscratch regs))
    (let mepc (get-reg mepc regs))
    (let mcause (get-reg mcause regs))
    (let mtval (get-reg mtval regs))
    (let mip (get-reg mip regs))
    (let mcycle (get-reg mcycle regs))
    (let minstret (get-reg minstret regs))
    (let mcycleh (get-reg mcycleh regs))
    (let minstreth (get-reg minstreth regs))
    (let frm (get-reg frm regs))
    (let fflags (get-reg fflags regs))
    (let fcsr (get-reg fcsr regs))
    (let priv (get-reg priv regs))
    (let exc (get-reg exc regs))
    (set-reg pc pc regs)
    (set-reg ra ra regs)
    (set-reg sp sp regs)
    (set-reg gp gp regs)
    (set-reg tp tp regs)
    (set-reg t0 t0 regs)
    (set-reg t1 t1 regs)
    (set-reg t2 t2 regs)
    (set-reg s0 s0 regs)
    (set-reg s1 s1 regs)
    (set-reg a0 a0 regs)
    (set-reg a1 a1 regs)
    (set-reg a2 a2 regs)
    (set-reg a3 a3 regs)
    (set-reg a4 a4 regs)
    (set-reg a5 a5 regs)
    (set-reg a6 a6 regs)
    (set-reg a7 a7 regs)
    (set-reg s2 s2 regs)
    (set-reg s3 s3 regs)
    (set-reg s4 s4 regs)
    (set-reg s5 s5 regs)
    (set-reg s6 s6 regs)
    (set-reg s7 s7 regs)
    (set-reg s8 s8 regs)
    (set-reg s9 s9 regs)
    (set-reg s10 s10 regs)
    (set-reg s11 s11 regs)
    (set-reg t3 t3 regs)
    (set-reg t4 t4 regs)
    (set-reg t5 t5 regs)
    (set-reg t6 t6 regs)
    (set-reg x1 x1 regs)
    (set-reg x2 x2 regs)
    (set-reg x3 x3 regs)
    (set-reg x4 x4 regs)
    (set-reg x5 x5 regs)
    (set-reg x6 x6 regs)
    (set-reg x7 x7 regs)
    (set-reg x8 x8 regs)
    (set-reg x9 x9 regs)
    (set-reg x10 x10 regs)
    (set-reg x11 x11 regs)
    (set-reg x12 x12 regs)
    (set-reg x13 x13 regs)
    (set-reg x14 x14 regs)
    (set-reg x15 x15 regs)
    (set-reg x16 x16 regs)
    (set-reg x17 x17 regs)
    (set-reg x18 x18 regs)
    (set-reg x19 x19 regs)
    (set-reg x20 x20 regs)
    (set-reg x21 x21 regs)
    (set-reg x22 x22 regs)
    (set-reg x23 x23 regs)
    (set-reg x24 x24 regs)
    (set-reg x25 x25 regs)
    (set-reg x26 x26 regs)
    (set-reg x27 x27 regs)
    (set-reg x28 x28 regs)
    (set-reg x29 x29 regs)
    (set-reg x30 x30 regs)
    (set-reg x31 x31 regs)
    (set-reg ft0 ft0 regs)
    (set-reg ft1 ft1 regs)
    (set-reg ft2 ft2 regs)
    (set-reg ft3 ft3 regs)
    (set-reg ft4 ft4 regs)
    (set-reg ft5 ft5 regs)
    (set-reg ft6 ft6 regs)
    (set-reg ft7 ft7 regs)
    (set-reg fs0 fs0 regs)
    (set-reg fs1 fs1 regs)
    (set-reg fa0 fa0 regs)
    (set-reg fa1 fa1 regs)
    (set-reg fa2 fa2 regs)
    (set-reg fa3 fa3 regs)
    (set-reg fa4 fa4 regs)
    (set-reg fa5 fa5 regs)
    (set-reg fa6 fa6 regs)
    (set-reg fa7 fa7 regs)
    (set-reg fs2 fs2 regs)
    (set-reg fs3 fs3 regs)
    (set-reg fs4 fs4 regs)
    (set-reg fs5 fs5 regs)
    (set-reg fs6 fs6 regs)
    (set-reg fs7 fs7 regs)
    (set-reg fs8 fs8 regs)
    (set-reg fs9 fs9 regs)
    (set-reg fs10 fs10 regs)
    (set-reg fs11 fs11 regs)
    (set-reg ft8 ft8 regs)
    (set-reg ft9 ft9 regs)
    (set-reg ft10 ft10 regs)
    (set-reg ft11 ft11 regs)
    (set-reg f0 f0 regs)
    (set-reg f1 f1 regs)
    (set-reg f2 f2 regs)
    (set-reg f3 f3 regs)
    (set-reg f4 f4 regs)
    (set-reg f5 f5 regs)
    (set-reg f6 f6 regs)
    (set-reg f7 f7 regs)
    (set-reg f8 f8 regs)
    (set-reg f9 f9 regs)
    (set-reg f10 f10 regs)
    (set-reg f11 f11 regs)
    (set-reg f12 f12 regs)
    (set-reg f13 f13 regs)
    (set-reg f14 f14 regs)
    (set-reg f15 f15 regs)
    (set-reg f16 f16 regs)
    (set-reg f17 f17 regs)
    (set-reg f18 f18 regs)
    (set-reg f19 f19 regs)
    (set-reg f20 f20 regs)
    (set-reg f21 f21 regs)
    (set-reg f22 f22 regs)
    (set-reg f23 f23 regs)
    (set-reg f24 f24 regs)
    (set-reg f25 f25 regs)
    (set-reg f26 f26 regs)
    (set-reg f27 f27 regs)
    (set-reg f28 f28 regs)
    (set-reg f29 f29 regs)
    (set-reg f30 f30 regs)
    (set-reg f31 f31 regs)
    (set-reg mvendorid mvendorid regs)
    (set-reg marchid marchid regs)
    (set-reg mimpid mimpid regs)
    (set-reg mhartid mhartid regs)
    (set-reg mstatus mstatus regs)
    (set-reg misa misa regs)
    (set-reg medeleg medeleg regs)
    (set-reg mideleg mideleg regs)
    (set-reg mie mie regs)
    (set-reg mtvec mtvec regs)
    (set-reg mcounteren mcounteren regs)
    (set-reg mscratch mscratch regs)
    (set-reg mepc mepc regs)
    (set-reg mcause mcause regs)
    (set-reg mtval mtval regs)
    (set-reg mip mip regs)
    (set-reg mcycle mcycle regs)
    (set-reg minstret minstret regs)
    (set-reg mcycleh mcycleh regs)
    (set-reg minstreth minstreth regs)
    (set-reg frm frm regs)
    (set-reg fflags fflags regs)
    (set-reg fcsr fcsr regs)
    (set-reg priv priv regs)
    (set-reg exc exc regs)
    (return regs)))
