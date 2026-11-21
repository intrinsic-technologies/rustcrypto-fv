import Hkdf.Proofs.NewExpand.Extract.State
import X86Proofs.Program.Execution
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.Entry

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def branchBytes : List UInt8 := [0x49,0x83,0xfe,0x3f,0x77,0x1b]

theorem dispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : CodeIn (codeRange 0x10fc63 branchBytes) s)
    (rip : s.RIP = 0x10fc63)
    (next : (0x10fc67 : BitVec 64) ≠ boundary.rip)
    (short : (0x10fc69 : BitVec 64) ≠ boundary.rip)
    (long : (0x10fc84 : BitVec 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .r14).toNat < 64 then 0x10fc69 else 0x10fc84) ∧
      AgreesExcept [.flags,.rip] s t := by
  obtain ⟨u, run, readyU, compared⟩ :=
    (cmp_r64_imm8_effect_step 0x10fc63 0x49 0xfe 0x3f
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (loaded.mono (codeRange_slice_subset 0x10fc63 branchBytes 0 4)) rip next
  have frame : AgreesExcept [.flags,.rip] s u := compared.agrees
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel8_effect_step 0x10fc67 7 0x1b u readyU
    ((frame.codeIn (by simp [Component.Covers]) loaded).mono
      (codeRange_slice_subset 0x10fc63 branchBytes 4 2))
    ⟨compared.rip, fun _ => by decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = (s.regValue .r14).ult 63 :=
    compared.flags.1
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .r14 - 63 == 0) :=
    compared.flags.2.2.2.1
  have target : t.RIP = (if (s.regValue .r14).toNat < 64 then 0x10fc69 else 0x10fc84) := by
    rw [jumped.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then 0x10fc84 else 0x10fc69) = _
    rw [carry, zero]
    have zeroEq : (s.regValue .r14 - 63 == 0) = decide ((s.regValue .r14).toNat = 63) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · exact congrArg BitVec.toNat
      · intro h
        apply BitVec.eq_of_toNat_eq
        exact h
    rw [zeroEq]
    have cond : (!((s.regValue .r14).ult 63 || decide ((s.regValue .r14).toNat = 63))) =
        decide (64 ≤ (s.regValue .r14).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [cond]
    by_cases small : (s.regValue .r14).toNat < 64
    · simp only [small, show ¬64 ≤ (s.regValue .r14).toNat by omega,
        decide_false, Bool.false_eq_true, ↓reduceIte]
    · simp only [small, show 64 ≤ (s.regValue .r14).toNat by omega, decide_true, ↓reduceIte]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact short
    · exact long
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect,branchEffect,Effect.components])⟩

end Hkdf.Proofs.NewExpand.Extract.Update
