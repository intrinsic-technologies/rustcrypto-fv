import P256.Proofs.Nonce.Update.Seeded.Finish.State
import P256.Proofs.Nonce.Update.Seeded.Finish.CopySetup
import P256.Proofs.Nonce.Update.Zero.CopyCall
import P256.Proofs.Nonce.Update.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {original state : State} {input : ByteArray}

theorem setup_copy (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Absorbed initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧
      CopyReady initial t state (state.value ++ ⟨#[1]⟩ ++ input) := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CopySetup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported)
    (programText_slice (programLoaded_codeIn current.loaded) 0xa849 CopySetup.bytes
      (by decide +kernel) (by decide +kernel)) current.rip
  have agrees : AgreesExcept [.reg 3, .reg 6, .reg 2, .reg 7, .rip] s t := by
    simpa only [CopySetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := current.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change t.regValue .rbx = stackPtr s + 432 ∧ t.regValue .rsi = stackPtr s + 256 ∧
    t.regValue .rdx = 168 ∧ t.regValue .rdi = stackPtr s + 432 at writes
  have rsp : stackPtr s = scratch initial := current.rsp
  refine ⟨fuel, t, run, ⟨frame, current.drbg.copy (by intros; rw [memory]), ?_⟩,
    effect.rip, ?_, ?_, ?_, writes.2.2.1, ?_⟩
  · rw [memory]; exact current.savedPointer
  · exact writes.2.1.trans (congrArg (· + 256) rsp)
  · exact writes.2.2.2.trans (congrArg (· + 432) rsp)
  · exact writes.1.trans (congrArg (· + 432) rsp)
  · exact current.hmac.copy (by intros; rw [memory])

theorem copy_hmac (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : CopyReady initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ Copied initial t state input := by
  let layout : StackCallLayout 1856 168 168 0 :=
    ⟨688, 424, 248, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
  have sourceAddress : scratch initial + 256 = stackPtr initial - 424 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have destinationAddress : scratch initial + 432 = stackPtr initial - 248 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨t, result⟩ := Zero.memcpy_call pre current.toFrameState layout rfl
    (by decide) (by decide) 0xa861 0xf9c91 (by decide) (by decide +kernel)
    (by decide +kernel) current.rip (current.source.trans sourceAddress)
    (current.destination.trans destinationAddress) current.count
  have drbg : DrbgAt t (initial.regValue .rdi) state := by
    apply current.drbg.copy
    intro i hi
    apply result.writes _
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (Update.Prepare.work_substack pre inside)
  have saved : memLoad t.external (scratch initial + 72) 64 = initial.regValue .rdi := by
    apply Eq.trans _ current.savedPointer
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    have address : scratch initial + 72 = stackPtr initial - 608 := by
      simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [address]
    exact result.preserved 608 8 (by decide) (by decide) (.inl (by decide)) i hi
  have hmac : HMAC.HmacStateAt t (scratch initial + 432) state.key input := by
    apply current.hmac.copy
    intro i hi
    rw [destinationAddress, sourceAddress]
    exact result.copied i hi
  obtain ⟨fuel, run⟩ := result.execution
  exact ⟨fuel, t, run, ⟨result.toFrameState, drbg, saved⟩, result.rip,
    (result.calleeSaved .rbx (by simp)).trans current.hashPointer, hmac⟩

end P256.Proofs.Nonce.Update.Seeded.Finish
