import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem borrow_difference {entry : BitVec 64} {s s1 s2 s3 t : RamState}
    {a p : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {high : BitVec 64} (input : Input s a high) (modulus : Modulus s p)
    (effect1 : (borrowLowEffect (entry+0x430) s).Holds s s1)
    (effect2 : (borrowMiddleEffect (entry+0x466) s1).Holds s1 s2)
    (effect3 : (borrowHighEffect (entry+0x49e) s2).Holds s2 s3)
    (effect4 : (borrowTopEffect (entry+0x4d6) s3).Holds s3 t) :
    Difference t (subRaw a p).1 (subRaw a p).2 := by
  let r0 := a.l0-p.l0
  let b0 := borrow a.l0 p.l0 r0
  let r1 := subWord a.l1 p.l1 b0
  let b1 := borrow a.l1 p.l1 r1
  let r2 := subWord a.l2 p.l2 b1
  let b2 := borrow a.l2 p.l2 r2
  let r3 := subWord a.l3 p.l3 b2
  let b3 := borrow a.l3 p.l3 r3
  have frame1 := borrowLow_frame effect1
  have frame2 := borrowMiddle_frame effect2
  have frame3 := borrowHigh_frame effect3
  have input1 := borrow_input frame1 input
  have input2 := borrow_input frame2 input1
  have input3 := borrow_input frame3 input2
  have modulus1 := borrow_modulus frame1 modulus
  have modulus2 := borrow_modulus frame2 modulus1
  have modulus3 := borrow_modulus frame3 modulus2
  have result0 : (Operand.reg 8 : Operand 64).read s1 = r0 := by
    have h : (Operand.reg 8 : Operand 64).read s1 =
        (Operand.reg 1 : Operand 64).read s -
          (Operand.mem (stackPtr s+32) : Operand 64).read s := effect1.writes.1
    rw [input.l0, modulus.l0] at h
    exact h
  have neg0 : (Operand.reg 9 : Operand 64).read s1 = -b0 := by
    have h : (Operand.reg 9 : Operand 64).read s1 =
        -borrow ((Operand.reg 1 : Operand 64).read s)
          ((Operand.mem (stackPtr s+32) : Operand 64).read s)
          ((Operand.reg 1 : Operand 64).read s -
            (Operand.mem (stackPtr s+32) : Operand 64).read s) := effect1.writes.2.2.1
    rw [input.l0, modulus.l0] at h
    exact h
  have result1 : (Operand.reg 9 : Operand 64).read s2 = r1 := by
    have h : (Operand.reg 9 : Operand 64).read s2 =
        ((Operand.reg 9 : Operand 64).read s1).sshiftRight 63 +
          ((Operand.reg 6 : Operand 64).read s1 - (Operand.mem (stackPtr s1+48) : Operand 64).read s1) := effect2.writes.1
    rw [input1.l1, modulus1.l1, neg0] at h
    exact h
  have neg1 : (Operand.reg 11 : Operand 64).read s2 = -b1 := by
    have h : (Operand.reg 11 : Operand 64).read s2 =
        -borrow ((Operand.reg 6 : Operand 64).read s1) ((Operand.mem (stackPtr s1+48) : Operand 64).read s1)
          (((Operand.reg 9 : Operand 64).read s1).sshiftRight 63 +
          ((Operand.reg 6 : Operand 64).read s1 - (Operand.mem (stackPtr s1+48) : Operand 64).read s1)) := effect2.writes.2.2.1
    rw [input1.l1, modulus1.l1, neg0] at h
    exact h
  have result2 : (Operand.reg 11 : Operand 64).read s3 = r2 := by
    have h : (Operand.reg 11 : Operand 64).read s3 =
        ((Operand.reg 11 : Operand 64).read s2).sshiftRight 63 +
          ((Operand.reg 0 : Operand 64).read s2 - (Operand.mem (stackPtr s2+40) : Operand 64).read s2) := effect3.writes.1
    rw [input2.l2, modulus2.l2, neg1] at h
    exact h
  have neg2 : (Operand.reg 14 : Operand 64).read s3 = -b2 := by
    have h : (Operand.reg 14 : Operand 64).read s3 =
        -borrow ((Operand.reg 0 : Operand 64).read s2) ((Operand.mem (stackPtr s2+40) : Operand 64).read s2)
          (((Operand.reg 11 : Operand 64).read s2).sshiftRight 63 +
          ((Operand.reg 0 : Operand 64).read s2 - (Operand.mem (stackPtr s2+40) : Operand 64).read s2)) := effect3.writes.2.2.1
    rw [input2.l2, modulus2.l2, neg1] at h
    exact h
  have result3 : (Operand.reg 14 : Operand 64).read t = r3 := by
    have h : (Operand.reg 14 : Operand 64).read t =
        ((Operand.reg 14 : Operand 64).read s3).sshiftRight 63 +
          ((Operand.reg 2 : Operand 64).read s3 - (Operand.reg 12 : Operand 64).read s3) := effect4.writes.1
    rw [input3.l3, modulus3.l3, neg2] at h
    exact h
  have neg3 : (Operand.reg 13 : Operand 64).read t = -b3 := by
    have h : (Operand.reg 13 : Operand 64).read t =
        -borrow ((Operand.reg 2 : Operand 64).read s3) ((Operand.reg 12 : Operand 64).read s3)
          (((Operand.reg 14 : Operand 64).read s3).sshiftRight 63 +
          ((Operand.reg 2 : Operand 64).read s3 - (Operand.reg 12 : Operand 64).read s3)) := effect4.writes.2.1
    rw [input3.l3, modulus3.l3, neg2] at h
    exact h
  have final0 : (Operand.reg 8 : Operand 64).read t = r0 := ((effect4.agrees.read (r := 8) (n := 64) (by simp [borrowTopEffect, Effect.components])).trans (((effect3.agrees.read (r := 8) (n := 64) (by simp [borrowHighEffect, Effect.components])).trans (((effect2.agrees.read (r := 8) (n := 64) (by simp [borrowMiddleEffect, Effect.components])).trans (result0))))))
  have final1 : (Operand.reg 9 : Operand 64).read t = r1 := ((effect4.agrees.read (r := 9) (n := 64) (by simp [borrowTopEffect, Effect.components])).trans (((effect3.agrees.read (r := 9) (n := 64) (by simp [borrowHighEffect, Effect.components])).trans (result1))))
  have final2 : (Operand.reg 11 : Operand 64).read t = r2 := ((effect4.agrees.read (r := 11) (n := 64) (by simp [borrowTopEffect, Effect.components])).trans (result2))
  exact ⟨final0, final1, final2, result3, neg3⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
