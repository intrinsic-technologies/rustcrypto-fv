import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XLowWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XSecondSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XSecondWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XThirdSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XThirdWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XHighSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XHighWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.XValidity
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.Frame
import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction (subtractModulus subtractModulus_borrow)

def xInput (t : RamState) : Limbs := ⟨(Operand.reg 2 : Operand 64).read t,(Operand.reg 6 : Operand 64).read t,(Operand.reg 1 : Operand 64).read t,(Operand.reg 0 : Operand 64).read t⟩

theorem x_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11085c)
    (r15 : t.regValue .r15 = 0xffffffff00000001)
    (r12 : t.regValue .r12 = 0xffffffff) (r13 : t.regValue .r13 = 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1108d8 ∧
      u.regValue .rbp = (if (xInput t).toNat < Operations.domain.p then 1 else 0) ∧
      AgreesExcept (components false t) t u  := by
  change (Operand.reg 15 : Operand 64).read t = _ at r15
  change (Operand.reg 12 : Operand 64).read t = _ at r12
  change (Operand.reg 13 : Operand 64).read t = _ at r13
  obtain ⟨n0,t0,r0,s0,e0,f0⟩ := run false pre state
    (offset := 0x1085c) (x_low_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) rip
    (by simp [xLowWordEffect, Effect.components, components])
  obtain ⟨n1,t1,r1,s1,e1,f1⟩ := run false pre s0
    (offset := 0x1086a) (x_second_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s0 e0.rip)
    (by simp [xSecondSetupEffect, Effect.components, components])
  have g1 := agrees_trans f0 f1
  obtain ⟨n2,t2,r2,s2,e2,f2⟩ := run false pre s1
    (offset := 0x1087f) (x_second_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e1.rip
    (by simp [xSecondWordEffect, Effect.components, components])
  have g2 := agrees_trans g1 f2
  obtain ⟨n3,t3,r3,s3,e3,f3⟩ := run false pre s2
    (offset := 0x1088f) (x_third_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s2 e2.rip)
    (by simp [xThirdSetupEffect, Effect.components, components])
  have g3 := agrees_trans g2 f3
  obtain ⟨n4,t4,r4,s4,e4,f4⟩ := run false pre s3
    (offset := 0x1089f) (x_third_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e3.rip
    (by simp [xThirdWordEffect, Effect.components, components])
  have g4 := agrees_trans g3 f4
  obtain ⟨n5,t5,r5,s5,e5,f5⟩ := run false pre s4
    (offset := 0x108ac) (x_high_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s4 e4.rip)
    (by simp [xHighSetupEffect, Effect.components, components])
  have g5 := agrees_trans g4 f5
  obtain ⟨n6,t6,r6,s6,e6,f6⟩ := run false pre s5
    (offset := 0x108ba) (x_high_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e5.rip
    (by simp [xHighWordEffect, Effect.components, components])
  have g6 := agrees_trans g5 f6
  obtain ⟨n7,t7,r7,s7,e7,f7⟩ := run false pre s6
    (offset := 0x108ca) (x_validity_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s6 e6.rip)
    (by simp [xValidityEffect, Effect.components, components])
  have g7 := agrees_trans g6 f7
  have limb1 : (Operand.reg 6 : Operand 64).read t1 =
      (Operand.reg 6 : Operand 64).read t :=
    (e0.agrees.trans e1.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, Effect.components])
  have limb2 : (Operand.reg 1 : Operand 64).read t3 =
      (Operand.reg 1 : Operand 64).read t :=
    (((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, xSecondWordEffect, xThirdSetupEffect, Effect.components])
  have limb3 : (Operand.reg 0 : Operand 64).read t5 =
      (Operand.reg 0 : Operand 64).read t :=
    (((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, xSecondWordEffect, xThirdSetupEffect, xThirdWordEffect, xHighSetupEffect, Effect.components])
  have constant1 : (Operand.reg 15 : Operand 64).read t1 =
      (Operand.reg 15 : Operand 64).read t :=
    (e0.agrees.trans e1.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, Effect.components])
  have constant3 : (Operand.reg 12 : Operand 64).read t5 =
      (Operand.reg 12 : Operand 64).read t :=
    (((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, xSecondWordEffect, xThirdSetupEffect, xThirdWordEffect, xHighSetupEffect, Effect.components])
  have initialBorrow : (Operand.reg 13 : Operand 64).read t4 =
      (Operand.reg 13 : Operand 64).read t :=
    ((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).read (by simp [xLowWordEffect, xSecondSetupEffect, xSecondWordEffect, xThirdSetupEffect, xThirdWordEffect, Effect.components])
  have w0 := e0.writes
  simp only [xLowWordEffect, Write.AllHold] at w0
  have w1 := e1.writes
  simp only [xSecondSetupEffect, Write.AllHold] at w1
  rw [w0.2] at w1
  have w2 := e2.writes
  simp only [xSecondWordEffect, Write.AllHold] at w2
  rw [limb1, constant1, r15, w1.2.2] at w2
  have w3 := e3.writes
  simp only [xThirdSetupEffect, Write.AllHold] at w3
  rw [w2.2] at w3
  have w4 := e4.writes
  simp only [xThirdWordEffect, Write.AllHold] at w4
  rw [limb2, w3.2] at w4
  have w5 := e5.writes
  simp only [xHighSetupEffect, Write.AllHold] at w5
  rw [initialBorrow, r13, w4.2] at w5
  have w6 := e6.writes
  simp only [xHighWordEffect, Write.AllHold] at w6
  rw [limb3, constant3, r12, w5.2] at w6
  have borrow : t6.regValue .rax = (subtractModulus (xInput t)).2 := by
    apply w6.2.trans
    simp only [subtractModulus, xInput]
    have hac (a b c : BitVec 64) : a + (b + c) = b + (a + c) := by
      rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]
    simp only [BitVec.add_comm, hac]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_sub, BitVec.add_assoc]
  have flag : (subtractModulus (xInput t)).2 =
      if (xInput t).toNat < Operations.domain.p then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := subtractModulus_borrow (xInput t)
    by_cases hx : (xInput t).toNat < Operations.domain.p <;> simpa [hx] using h
  have val := e7.writes.2
  change t7.regValue .rbp = ((t6.regValue .rax).setWidth 8 &&& 1).setWidth 64 at val
  rw [borrow,flag] at val
  refine ⟨n0+n1+n2+n3+n4+n5+n6+n7,t7,
    ((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r6).trans r7,
    s7,e7.rip,?_,g7⟩
  · by_cases hx : (xInput t).toNat < Operations.domain.p <;> simpa [hx] using val

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
