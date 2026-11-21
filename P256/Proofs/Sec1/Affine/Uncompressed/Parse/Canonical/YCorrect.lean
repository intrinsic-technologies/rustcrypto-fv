import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YLowWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YSecondSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YSecondWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YThirdSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YThirdWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YHighSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YHighWord
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.YValidity
import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.Frame
import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction (subtractModulus subtractModulus_borrow)

def yInput (t : RamState) : Limbs := ⟨(Operand.reg 2 : Operand 64).read t,(Operand.reg 7 : Operand 64).read t,(Operand.reg 1 : Operand 64).read t,(Operand.reg 0 : Operand 64).read t⟩

theorem y_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110671) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110704 ∧
      u.regValue .r14 = (if (yInput t).toNat < Operations.domain.p then 1 else 0) ∧
      u.regValue .r15 = 0xffffffff00000001 ∧
      u.regValue .r12 = 0xffffffff ∧ u.regValue .r13 = 0 ∧
      AgreesExcept (components true t) t u := by
  obtain ⟨n0,t0,r0,s0,e0,f0⟩ := run true pre state
    (offset := 0x10671) (y_low_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) rip
    (by simp [yLowWordEffect, Effect.components, components])
  obtain ⟨n1,t1,r1,s1,e1,f1⟩ := run true pre s0
    (offset := 0x1067f) (y_second_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s0 e0.rip)
    (by simp [ySecondSetupEffect, Effect.components, components])
  have g1 := agrees_trans f0 f1
  obtain ⟨n2,t2,r2,s2,e2,f2⟩ := run true pre s1
    (offset := 0x10695) (y_second_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e1.rip
    (by simp [ySecondWordEffect, Effect.components, components])
  have g2 := agrees_trans g1 f2
  obtain ⟨n3,t3,r3,s3,e3,f3⟩ := run true pre s2
    (offset := 0x106af) (y_third_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s2 e2.rip)
    (by simp [yThirdSetupEffect, Effect.components, components])
  have g3 := agrees_trans g2 f3
  obtain ⟨n4,t4,r4,s4,e4,f4⟩ := run true pre s3
    (offset := 0x106bf) (y_third_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e3.rip
    (by simp [yThirdWordEffect, Effect.components, components])
  have g4 := agrees_trans g3 f4
  obtain ⟨n5,t5,r5,s5,e5,f5⟩ := run true pre s4
    (offset := 0x106cc) (y_high_setup_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s4 e4.rip)
    (by simp [yHighSetupEffect, Effect.components, components])
  have g5 := agrees_trans g4 f5
  obtain ⟨n6,t6,r6,s6,e6,f6⟩ := run true pre s5
    (offset := 0x106df) (y_high_word_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) e5.rip
    (by simp [yHighWordEffect, Effect.components, components])
  have g6 := agrees_trans g5 f6
  obtain ⟨n7,t7,r7,s7,e7,f7⟩ := run true pre s6
    (offset := 0x106f5) (y_validity_correct boundary pre.outerBoundary)
    (by decide) (by decide +kernel) (borrow_pre pre s6 e6.rip)
    (by simp [yValidityEffect, Effect.components, components])
  have g7 := agrees_trans g6 f7
  have limb1 : (Operand.reg 7 : Operand 64).read t1 =
      (Operand.reg 7 : Operand 64).read t :=
    (e0.agrees.trans e1.agrees).read (by simp [yLowWordEffect, ySecondSetupEffect, Effect.components])
  have limb2 : (Operand.reg 1 : Operand 64).read t3 =
      (Operand.reg 1 : Operand 64).read t :=
    (((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).read (by simp [yLowWordEffect, ySecondSetupEffect, ySecondWordEffect, yThirdSetupEffect, Effect.components])
  have limb3 : (Operand.reg 0 : Operand 64).read t5 =
      (Operand.reg 0 : Operand 64).read t :=
    (((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).read (by simp [yLowWordEffect, ySecondSetupEffect, ySecondWordEffect, yThirdSetupEffect, yThirdWordEffect, yHighSetupEffect, Effect.components])
  have w0 := e0.writes
  simp only [yLowWordEffect, Write.AllHold] at w0
  have w1 := e1.writes
  simp only [ySecondSetupEffect, Write.AllHold] at w1
  rw [w0.2] at w1
  have w2 := e2.writes
  simp only [ySecondWordEffect, Write.AllHold] at w2
  rw [limb1, w1.2.2] at w2
  have w3 := e3.writes
  simp only [yThirdSetupEffect, Write.AllHold] at w3
  rw [w2.2.2] at w3
  have w4 := e4.writes
  simp only [yThirdWordEffect, Write.AllHold] at w4
  rw [limb2, w3.2] at w4
  have w5 := e5.writes
  simp only [yHighSetupEffect, Write.AllHold] at w5
  rw [w4.2] at w5
  have w6 := e6.writes
  simp only [yHighWordEffect, Write.AllHold] at w6
  rw [limb3, w5.2.2] at w6
  have borrow : t6.regValue .rax = (subtractModulus (yInput t)).2 := by
    apply w6.2.2.trans
    simp only [subtractModulus, yInput]
    simp only [BitVec.add_comm]
  have flag : (subtractModulus (yInput t)).2 =
      if (yInput t).toNat < Operations.domain.p then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := subtractModulus_borrow (yInput t)
    by_cases hx : (yInput t).toNat < Operations.domain.p <;> simpa [hx] using h
  have val := e7.writes.2
  change t7.regValue .r14 = ((t6.regValue .rax).setWidth 8 &&& 1).setWidth 64 at val
  rw [borrow,flag] at val
  refine ⟨n0+n1+n2+n3+n4+n5+n6+n7,t7,
    ((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r6).trans r7,
    s7,e7.rip,?_,?_,?_,?_,g7⟩
  · by_cases hx : (yInput t).toNat < Operations.domain.p <;> simpa [hx] using val
  · exact (((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).read (n := 64) (r := 15)
      (by simp [yThirdSetupEffect, yThirdWordEffect, yHighSetupEffect, yHighWordEffect, yValidityEffect, Effect.components])).trans e2.writes.1
  · exact (e7.agrees.read (n := 64) (r := 12)
      (by simp [yValidityEffect, Effect.components])).trans e6.writes.1
  · exact ((e6.agrees.trans e7.agrees).read (n := 64) (r := 13)
      (by simp [yHighWordEffect, yValidityEffect, Effect.components])).trans e5.writes.2.1

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
