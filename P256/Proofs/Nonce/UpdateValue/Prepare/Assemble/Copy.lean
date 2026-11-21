import P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.State
import P256.Proofs.Nonce.UpdateValue.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

private def copyLayout : StackCallLayout 1168 168 168 0 :=
  ⟨496, 216, 384, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem copy_hmac [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (current : CopyReady initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t state := by
  have source : s.regValue .rsi = stackPtr initial - 216 := by
    rw [current.source, scratch]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have destination : s.regValue .rdi = stackPtr initial - 384 := by
    rw [current.destination, scratch]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨t, result⟩ := memcpy_call pre current.toFrameState copyLayout rfl
    (by decide) (by decide) 0xaaed 0xf9a05 (by decide)
    (by decide +kernel) (by decide +kernel) current.rip source destination current.count
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨fuel, t, run, result.toFrameState, result.rip,
    (result.calleeSaved .rbx (by simp)).trans current.statePointer,
    (result.calleeSaved .r14 (by simp)).trans current.bufferPointer, ?_, ?_⟩
  · apply current.drbg.copy
    intro i hi
    apply result.writes
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1168 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (work_substack pre inside)
  · apply current.hmac.copy
    have sourceAddr : scratch initial + 272#64 = stackPtr initial - 216#64 := by
      simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    have targetAddr : scratch initial + 104#64 = stackPtr initial - 384#64 := by
      simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    simpa only [BitVec.ofNat_eq_ofNat, sourceAddr, targetAddr, copyLayout] using result.copied

end P256.Proofs.Nonce.UpdateValue.Prepare.Assemble
