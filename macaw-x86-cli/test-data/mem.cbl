; Test pointer-read and pointer-write
(defun @main () Unit
  (start start:
    ; Basic read/write
    (let p (global-ptr 0 0x1000))
    (let v1 (bv-typed-literal (Bitvector 64) 0xdeadbeef))
    (pointer-write (Bitvector 64) le p v1)
    (let r1 (pointer-read (Bitvector 64) le p))
    (assert! (equal? r1 v1) "basic write/read")

    ; Last write wins
    (let v2 (bv-typed-literal (Bitvector 64) 0xcafebabe))
    (pointer-write (Bitvector 64) le p v2)
    (let r2 (pointer-read (Bitvector 64) le p))
    (assert! (equal? r2 v2) "last write wins")

    ; Different sizes at same location
    (let p2 (global-ptr 0 0x2000))
    (let v32 (bv-typed-literal (Bitvector 32) 0x12345678))
    (pointer-write (Bitvector 32) le p2 v32)
    (let r32 (pointer-read (Bitvector 32) le p2))
    (assert! (equal? r32 v32) "32-bit write/read")

    (let v8 (bv-typed-literal (Bitvector 8) 0xaa))
    (pointer-write (Bitvector 8) le p2 v8)
    (let r8 (pointer-read (Bitvector 8) le p2))
    (assert! (equal? r8 v8) "8-bit overwrites low byte")

    ; Read from uninitialized memory - returns a symbolic value, doesn't fail
    (let p3 (global-ptr 0 0x3000))
    (pointer-read (Bitvector 64) le p3)

    ; Write to a bad allocation number
    (let p4 (global-ptr 99 0xffffffffffffffff))
    (let v0 (bv-typed-literal (Bitvector 64) 0))
    (pointer-write (Bitvector 64) le p4 v0)

    (return ())))
