import P256.Proofs.Field.Subtract.Body

set_option autoImplicit false

namespace P256.Proofs.Field.Subtract

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open X86 X86.Machine X86.UserProcess X86Proofs

def outputLimbs (s : RamState) : Limbs :=
  ⟨s.regValue .rsi, s.regValue .r9, s.regValue .r11, s.regValue .rdx⟩

theorem body_value {s t : RamState} (trace : BodyTrace s t) :
    outputLimbs t = subLimbs (readLimbs s (s.regValue .rsi)) (readLimbs s (s.regValue .rdx)) := by
  obtain ⟨s1, s2, s3, s4, s5, e1, e2, e3, e4, e5, e6⟩ := trace
  have zsub (v : BitVec 64) : (0 : BitVec 64) - v = -v := by
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_sub]
  let a := readLimbs s (s.regValue .rsi)
  let b := readLimbs s (s.regValue .rdx)
  let r0 := a.l0-b.l0
  let q0 := borrow a.l0 b.l0 r0
  let r1 := subWord a.l1 b.l1 q0
  let q1 := borrow a.l1 b.l1 r1
  let r2 := subWord a.l2 b.l2 q1
  let q2 := borrow a.l2 b.l2 r2
  let r3 := subWord a.l3 b.l3 q2
  let q3 := borrow a.l3 b.l3 r3
  have h1_9 : (Operand.reg 9 : Operand 64).read s1 = a.l0 := by
    have hw : (Operand.reg 9 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rsi + 0) 64 := e1.writes.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_8 : (Operand.reg 8 : Operand 64).read s1 = a.l1 := by
    have hw : (Operand.reg 8 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rsi + 8) 64 := e1.writes.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_10 : (Operand.reg 10 : Operand 64).read s1 = a.l2 := by
    have hw : (Operand.reg 10 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rsi + 16) 64 := e1.writes.2.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_1 : (Operand.reg 1 : Operand 64).read s1 = a.l3 := by
    have hw : (Operand.reg 1 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rsi + 24) 64 := e1.writes.2.2.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_14 : (Operand.reg 14 : Operand 64).read s1 = b.l0 := by
    have hw : (Operand.reg 14 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rdx + 0) 64 := e1.writes.2.2.2.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_3 : (Operand.reg 3 : Operand 64).read s1 = b.l1 := by
    have hw : (Operand.reg 3 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rdx + 8) 64 := e1.writes.2.2.2.2.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_11 : (Operand.reg 11 : Operand 64).read s1 = b.l2 := by
    have hw : (Operand.reg 11 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rdx + 16) 64 := e1.writes.2.2.2.2.2.2.1
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h1_6 : (Operand.reg 6 : Operand 64).read s1 = b.l3 := by
    have hw : (Operand.reg 6 : Operand 64).read s1 =
        memLoad s.external (s.regValue .rdx + 24) 64 := e1.writes.2.2.2.2.2.2.2
    simpa only [a, b, readLimbs, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  have h2_0 : (Operand.reg 0 : Operand 64).read s2 = r0 := by
    have hw := e2.writes.1
    simpa only [borrowLowEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h1_9, h1_8, h1_10, h1_1, h1_14, h1_3, h1_11, h1_6, zsub] using hw
  have h2_9 : (Operand.reg 9 : Operand 64).read s2 = 0 := by
    have hw := e2.writes.2.1
    simpa only [borrowLowEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h1_9, h1_8, h1_10, h1_1, h1_14, h1_3, h1_11, h1_6, zsub] using hw
  have h2_2 : (Operand.reg 2 : Operand 64).read s2 = -q0 := by
    have hw := e2.writes.2.2.1
    simpa only [borrowLowEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h1_9, h1_8, h1_10, h1_1, h1_14, h1_3, h1_11, h1_6, zsub] using hw
  have h2_8 : (Operand.reg 8 : Operand 64).read s2 = a.l1 :=
    (e2.agrees.read (n := 64) (r := 8) (by simp [borrowLowEffect, Effect.components])).trans h1_8
  have h2_10 : (Operand.reg 10 : Operand 64).read s2 = a.l2 :=
    (e2.agrees.read (n := 64) (r := 10) (by simp [borrowLowEffect, Effect.components])).trans h1_10
  have h2_1 : (Operand.reg 1 : Operand 64).read s2 = a.l3 :=
    (e2.agrees.read (n := 64) (r := 1) (by simp [borrowLowEffect, Effect.components])).trans h1_1
  have h2_3 : (Operand.reg 3 : Operand 64).read s2 = b.l1 :=
    (e2.agrees.read (n := 64) (r := 3) (by simp [borrowLowEffect, Effect.components])).trans h1_3
  have h2_11 : (Operand.reg 11 : Operand 64).read s2 = b.l2 :=
    (e2.agrees.read (n := 64) (r := 11) (by simp [borrowLowEffect, Effect.components])).trans h1_11
  have h2_6 : (Operand.reg 6 : Operand 64).read s2 = b.l3 :=
    (e2.agrees.read (n := 64) (r := 6) (by simp [borrowLowEffect, Effect.components])).trans h1_6
  have h3_2 : (Operand.reg 2 : Operand 64).read s3 = r1 := by
    have hw := e3.writes.2.1
    simpa only [borrowMiddleEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h2_0, h2_9, h2_2, h2_8, h2_10, h2_1, h2_3, h2_11, h2_6, zsub] using hw
  have h3_8 : (Operand.reg 8 : Operand 64).read s3 = 0 := by
    have hw := e3.writes.2.2.1
    simpa only [borrowMiddleEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h2_0, h2_9, h2_2, h2_8, h2_10, h2_1, h2_3, h2_11, h2_6, zsub] using hw
  have mem3 : (Operand.mem (stackPtr s3) : Operand 64).read s3 = q1 := by
    have sp : stackPtr s3 = stackPtr s2 :=
      e3.agrees.read (n := 64) (r := 4) (by simp [borrowMiddleEffect, Effect.components])
    rw [sp]
    have hw := e3.writes.2.2.2
    change (Operand.mem (stackPtr s2) : Operand 64).read s3 = _ at hw
    simpa only [borrowMiddleEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h2_0, h2_9, h2_2, h2_8, h2_10, h2_1, h2_3, h2_11, h2_6, zsub] using hw
  have h3_0 : (Operand.reg 0 : Operand 64).read s3 = r0 :=
    (e3.agrees.read (n := 64) (r := 0) (by simp [borrowMiddleEffect, Effect.components])).trans h2_0
  have h3_9 : (Operand.reg 9 : Operand 64).read s3 = 0 :=
    (e3.agrees.read (n := 64) (r := 9) (by simp [borrowMiddleEffect, Effect.components])).trans h2_9
  have h3_10 : (Operand.reg 10 : Operand 64).read s3 = a.l2 :=
    (e3.agrees.read (n := 64) (r := 10) (by simp [borrowMiddleEffect, Effect.components])).trans h2_10
  have h3_1 : (Operand.reg 1 : Operand 64).read s3 = a.l3 :=
    (e3.agrees.read (n := 64) (r := 1) (by simp [borrowMiddleEffect, Effect.components])).trans h2_1
  have h3_11 : (Operand.reg 11 : Operand 64).read s3 = b.l2 :=
    (e3.agrees.read (n := 64) (r := 11) (by simp [borrowMiddleEffect, Effect.components])).trans h2_11
  have h3_6 : (Operand.reg 6 : Operand 64).read s3 = b.l3 :=
    (e3.agrees.read (n := 64) (r := 6) (by simp [borrowMiddleEffect, Effect.components])).trans h2_6
  have h4_8 : (Operand.reg 8 : Operand 64).read s4 = r2 := by
    have hw := e4.writes.2.1
    simpa only [borrowHighEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h3_2, h3_8, h3_0, h3_9, h3_10, h3_1, h3_11, h3_6, mem3, zsub] using hw
  have h4_10 : (Operand.reg 10 : Operand 64).read s4 = 0 := by
    have hw := e4.writes.2.2.1
    simpa only [borrowHighEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h3_2, h3_8, h3_0, h3_9, h3_10, h3_1, h3_11, h3_6, mem3, zsub] using hw
  have mem4 : (Operand.mem (stackPtr s4) : Operand 64).read s4 = q2 := by
    have sp : stackPtr s4 = stackPtr s3 :=
      e4.agrees.read (n := 64) (r := 4) (by simp [borrowHighEffect, Effect.components])
    rw [sp]
    have hw := e4.writes.2.2.2
    change (Operand.mem (stackPtr s3) : Operand 64).read s4 = _ at hw
    simpa only [borrowHighEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h3_2, h3_8, h3_0, h3_9, h3_10, h3_1, h3_11, h3_6, mem3, zsub] using hw
  have h4_0 : (Operand.reg 0 : Operand 64).read s4 = r0 :=
    (e4.agrees.read (n := 64) (r := 0) (by simp [borrowHighEffect, Effect.components])).trans h3_0
  have h4_2 : (Operand.reg 2 : Operand 64).read s4 = r1 :=
    (e4.agrees.read (n := 64) (r := 2) (by simp [borrowHighEffect, Effect.components])).trans h3_2
  have h4_9 : (Operand.reg 9 : Operand 64).read s4 = 0 :=
    (e4.agrees.read (n := 64) (r := 9) (by simp [borrowHighEffect, Effect.components])).trans h3_9
  have h4_1 : (Operand.reg 1 : Operand 64).read s4 = a.l3 :=
    (e4.agrees.read (n := 64) (r := 1) (by simp [borrowHighEffect, Effect.components])).trans h3_1
  have h4_6 : (Operand.reg 6 : Operand 64).read s4 = b.l3 :=
    (e4.agrees.read (n := 64) (r := 6) (by simp [borrowHighEffect, Effect.components])).trans h3_6
  have h5_10 : (Operand.reg 10 : Operand 64).read s5 = r3 := by
    have hw := e5.writes.2.1
    simpa only [borrowTopEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h4_8, h4_10, h4_0, h4_2, h4_9, h4_1, h4_6, mem4, zsub] using hw
  have h5_1 : (Operand.reg 1 : Operand 64).read s5 = (-q3) >>> 63 := by
    have hw := e5.writes.2.2.2.1
    simpa only [borrowTopEffect, borrow, subWord, r0, q0, r1, q1, r2, q2, r3, q3, h4_8, h4_10, h4_0, h4_2, h4_9, h4_1, h4_6, mem4, zsub] using hw
  have h5_0 : (Operand.reg 0 : Operand 64).read s5 = r0 :=
    (e5.agrees.read (n := 64) (r := 0) (by simp [borrowTopEffect, Effect.components])).trans h4_0
  have h5_2 : (Operand.reg 2 : Operand 64).read s5 = r1 :=
    (e5.agrees.read (n := 64) (r := 2) (by simp [borrowTopEffect, Effect.components])).trans h4_2
  have h5_8 : (Operand.reg 8 : Operand 64).read s5 = r2 :=
    (e5.agrees.read (n := 64) (r := 8) (by simp [borrowTopEffect, Effect.components])).trans h4_8
  have raw : (⟨s5.regValue .rax, s5.regValue .rdx, s5.regValue .r8, s5.regValue .r10⟩ : Limbs) = (subRaw a b).1 := by
    change (⟨(Operand.reg 0 : Operand 64).read s5, (Operand.reg 2 : Operand 64).read s5, (Operand.reg 8 : Operand 64).read s5, (Operand.reg 10 : Operand 64).read s5⟩ : Limbs) = _
    rw [h5_0, h5_2, h5_8, h5_10]
    rfl
  have mask : s5.regValue .rcx = (-(subRaw a b).2) >>> 63 := h5_1
  have hw := e6.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  change (⟨(Operand.reg 6 : Operand 64).read t, (Operand.reg 9 : Operand 64).read t, (Operand.reg 11 : Operand 64).read t, (Operand.reg 2 : Operand 64).read t⟩ : Limbs) = _
  rw [hw.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1]
  change correct _ _ = _
  rw [raw, mask]
  rfl

end P256.Proofs.Field.Subtract
