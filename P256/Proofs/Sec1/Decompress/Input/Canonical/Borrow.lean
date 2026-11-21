import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic
import P256.Proofs.Sec1.Decompress.Input.Canonical.Frame
import P256.Proofs.Sec1.Decompress.Input.Canonical.LowWord
import P256.Proofs.Sec1.Decompress.Input.Canonical.SecondWord
import P256.Proofs.Sec1.Decompress.Input.Canonical.SecondArithmetic
import P256.Proofs.Sec1.Decompress.Input.Canonical.ThirdWord
import P256.Proofs.Sec1.Decompress.Input.Canonical.HighArithmetic

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction (subtractModulus)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalInput (s : RamState) : Limbs :=
  ⟨(Operand.reg 2 : Operand 64).read s, (Operand.reg 8 : Operand 64).read s,
    (Operand.reg 1 : Operand 64).read s, (Operand.reg 0 : Operand 64).read s⟩

theorem canonical_trans {s t u : RamState} (h : AgreesExcept (canonicalFrame s) s t)
    (h' : AgreesExcept (canonicalFrame t) t u) : AgreesExcept (canonicalFrame s) s u := by
  rw [canonical_frame_eq (canonical_stack h)] at h'
  exact (h.trans h').mono (by simp)

theorem canonical_borrow_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : CanonicalPre 0x10fc44 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      CanonicalPre 0x10fcc5 t ∧ AgreesExcept (canonicalFrame s) s t ∧
      (Operand.reg 0 : Operand 64).read t = (subtractModulus (canonicalInput s)).2 ∧
      (Operand.mem (stackPtr s + 184#64) : Operand 64).read t =
        (Operand.reg 7 : Operand 64).read s ∧
      (Operand.reg 14 : Operand 64).read t = 0xffffffff00000001 := by
  obtain ⟨n0, t0, run0, rd0, ld0, p0, h0, f0⟩ :=
    canonical_run (s := s) (q := 0x10fc52) (offset := 0xfc44)
      (canonical_low_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      ready loaded pre pre.rip rfl
      (by simp [canonicalLowWordEffect, Effect.components, canonicalFrame])
  have g0 := f0
  obtain ⟨n1, t1, run1, rd1, ld1, p1, h1, f1⟩ :=
    canonical_run (s := t0) (q := 0x10fc66) (offset := 0xfc52)
      (canonical_borrow_setup_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd0 ld0 p0 p0.toBorrowSlotPre rfl
      (by simp [canonicalBorrowSetupEffect, Effect.components, canonicalFrame])
  have g1 := canonical_trans g0 f1
  obtain ⟨n2, t2, run2, rd2, ld2, p2, h2, f2⟩ :=
    canonical_run (s := t1) (q := 0x10fc80) (offset := 0xfc66)
      (canonical_second_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd1 ld1 p1 p1.rip rfl
      (by simp [canonicalSecondWordEffect, Effect.components, canonicalFrame])
  have g2 := canonical_trans g1 f2
  obtain ⟨n3, t3, run3, rd3, ld3, p3, h3, f3⟩ :=
    canonical_run (s := t2) (q := 0x10fc8f) (offset := 0xfc80)
      (canonical_third_setup_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd2 ld2 p2 p2.toBorrowSlotPre rfl
      (by simp [canonicalThirdSetupEffect, Effect.components, canonicalFrame])
  have g3 := canonical_trans g2 f3
  obtain ⟨n4, t4, run4, rd4, ld4, p4, h4, f4⟩ :=
    canonical_run (s := t3) (q := 0x10fc9c) (offset := 0xfc8f)
      (canonical_third_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd3 ld3 p3 p3.rip rfl
      (by simp [canonicalThirdWordEffect, Effect.components, canonicalFrame])
  have g4 := canonical_trans g3 f4
  obtain ⟨n5, t5, run5, rd5, ld5, p5, h5, f5⟩ :=
    canonical_run (s := t4) (q := 0x10fcb0) (offset := 0xfc9c)
      (canonical_high_setup_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd4 ld4 p4 p4 rfl
      (by simp [canonicalHighSetupEffect, Effect.components, canonicalFrame])
  have g5 := canonical_trans g4 f5
  obtain ⟨n6, t6, run6, rd6, ld6, p6, h6, f6⟩ :=
    canonical_run (s := t5) (q := 0x10fcc5) (offset := 0xfcb0)
      (canonical_high_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd5 ld5 p5 p5.rip rfl
      (by simp [canonicalHighWordEffect, Effect.components, canonicalFrame])
  have g6 := canonical_trans g5 f6
  have w0 := h0.writes
  change (Operand.reg 6 : Operand 64).read t0 = (canonicalInput s).l0 + 1 ∧
    (Operand.reg 2 : Operand 64).read t0 =
      (~~~(canonicalInput s).l0 ||| ((canonicalInput s).l0 + 1)) >>> 63 at w0
  have w1 := h1.writes
  simp only [canonicalBorrowSetupEffect, Write.AllHold] at w1
  rw [w0.2] at w1
  have x1 : (Operand.reg 8 : Operand 64).read t1 =
      (Operand.reg 8 : Operand 64).read s :=
    (h0.agrees.trans h1.agrees).read (by simp [canonicalLowWordEffect, canonicalBorrowSetupEffect, Effect.components])
  have x2 : (Operand.reg 1 : Operand 64).read t3 =
      (Operand.reg 1 : Operand 64).read s :=
    (((h0.agrees.trans h1.agrees).trans h2.agrees).trans h3.agrees).read (by simp [canonicalLowWordEffect, canonicalBorrowSetupEffect, canonicalSecondWordEffect, canonicalThirdSetupEffect, Effect.components])
  have x3 : (Operand.reg 0 : Operand 64).read t5 =
      (Operand.reg 0 : Operand 64).read s :=
    (((((h0.agrees.trans h1.agrees).trans h2.agrees).trans h3.agrees).trans h4.agrees).trans h5.agrees).read (by simp [canonicalLowWordEffect, canonicalBorrowSetupEffect, canonicalSecondWordEffect, canonicalThirdSetupEffect, canonicalThirdWordEffect, canonicalHighSetupEffect, Effect.components])
  have ptr : (Operand.reg 7 : Operand 64).read t4 =
      (Operand.reg 7 : Operand 64).read s :=
    ((((h0.agrees.trans h1.agrees).trans h2.agrees).trans h3.agrees).trans h4.agrees).read (by simp [canonicalLowWordEffect, canonicalBorrowSetupEffect, canonicalSecondWordEffect, canonicalThirdSetupEffect, canonicalThirdWordEffect, Effect.components])
  have zero : (Operand.reg 6 : Operand 64).read t4 =
      (Operand.reg 6 : Operand 64).read t1 :=
    ((h2.agrees.trans h3.agrees).trans h4.agrees).read (by simp [canonicalSecondWordEffect, canonicalThirdSetupEffect, canonicalThirdWordEffect, Effect.components])
  have w2 := h2.writes
  simp only [canonicalSecondWordEffect, Write.AllHold] at w2
  rw [x1, w1.2.2.2] at w2
  have w3 := h3.writes
  simp only [canonicalThirdSetupEffect, Write.AllHold] at w3
  rw [w2.2.2] at w3
  have w4 := h4.writes
  simp only [canonicalThirdWordEffect, Write.AllHold] at w4
  rw [x2, w3.2] at w4
  have w5 := h5.writes
  simp only [canonicalHighSetupEffect, Write.AllHold] at w5
  rw [ptr, zero, w1.2.2.1, w4.2] at w5
  have w6 := h6.writes
  simp only [canonicalHighWordEffect, Write.AllHold] at w6
  rw [x3, w5.2.2] at w6
  refine ⟨n0+n1+n2+n3+n4+n5+n6, t6,
    (((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6,
    rd6, ld6, p6, g6, ?_, ?_, ?_⟩
  · apply w6.2.2.trans
    simp only [subtractModulus, canonicalInput]
    have hac (a b c : BitVec 64) : a + (b + c) = b + (a + c) := by
      rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]
    simp only [BitVec.add_comm, hac]
    have hz (x : BitVec 64) : (0 : BitVec 64) - x = -x := BitVec.zero_sub x
    simp only [hz]
  · have hm : t6.external = t5.external := h6.agrees.external
      (by simp [canonicalHighWordEffect, Effect.components, Component.Covers])
    change memLoad t6.external (stackPtr s + 184#64) 64 = _
    rw [hm]
    have hh := w5.2.1
    rw [canonical_stack g4] at hh
    exact hh

  · exact ((((h3.agrees.trans h4.agrees).trans h5.agrees).trans h6.agrees).read
      (n := 64) (r := 14) (by simp [canonicalThirdSetupEffect, canonicalThirdWordEffect,
        canonicalHighSetupEffect, canonicalHighWordEffect, Effect.components])).trans h2.writes.1

end P256.Proofs.Sec1.Decompress.Input
