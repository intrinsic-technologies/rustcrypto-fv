import P256.Proofs.Nonce.Update.Zero.CopyCall
import P256.Proofs.Nonce.Update.Zero.CopySetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem setup_copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (current : Absorbed initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧
      CopyReady initial t state (state.value ++ ⟨#[0]⟩ ++ input.seed) := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CopySetup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported)
    (programText_slice (programLoaded_codeIn current.loaded) 0xa39c CopySetup.bytes
      (by decide +kernel) (by decide +kernel)) current.rip
  have agrees : AgreesExcept [.reg 3, .reg 6, .reg 2, .reg 7, .rip] s t := by
    simpa only [CopySetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := current.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp)
  have old : Context initial s state := ⟨current.toFrameState, current.drbg,
    current.savedPointer, current.savedValue, current.savedCount, current.descriptors, current.savedEnd⟩
  have context := old.of_copied frame (current.drbg.copy (by intros; rw [memory]))
    ((agrees.read (n := 64) (r := 5) (by simp)).trans current.descriptors)
    (by intros; rw [memory])
  have writes := effect.writes
  change t.regValue .rbx = stackPtr s + 432 ∧ t.regValue .rsi = stackPtr s + 88 ∧
    t.regValue .rdx = 168 ∧ t.regValue .rdi = stackPtr s + 432 at writes
  have rsp : stackPtr s = scratch initial := current.rsp
  refine ⟨fuel, t, run, context, effect.rip, ?_, ?_, ?_, writes.2.2.1, ?_⟩
  · exact writes.2.1.trans (congrArg (· + 88) rsp)
  · exact writes.2.2.2.trans (congrArg (· + 432) rsp)
  · exact writes.1.trans (congrArg (· + 432) rsp)
  · exact current.hmac.copy (by intros; rw [memory])

def copyLayout : StackCallLayout 1856 168 168 0 :=
  ⟨688, 592, 248, by decide, by decide, by decide, by decide,
    by decide, by decide, .inl (by decide)⟩

theorem copy_hmac [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : CopyReady initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ Copied initial t state input := by
  have sourceAddress : scratch initial + 88#64 = stackPtr initial - 592#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have destinationAddress : scratch initial + 432#64 = stackPtr initial - 248#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have source : s.regValue .rsi = stackPtr initial - 592#64 := by
    simpa only [BitVec.ofNat_eq_ofNat, sourceAddress] using current.source
  have destination : s.regValue .rdi = stackPtr initial - 248#64 := by
    simpa only [BitVec.ofNat_eq_ofNat, destinationAddress] using current.destination
  obtain ⟨t, result⟩ := memcpy_call pre current.toFrameState copyLayout rfl
    (by decide) (by decide) 0xa3b1 0xfa141 (by decide)
    (by decide +kernel) (by decide +kernel) current.rip source destination current.count
  have drbg : DrbgAt t (initial.regValue .rdi) state := by
    apply current.drbg.of_frame pre.stateBounded result.writes
    intro region member a ha hb
    have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
    subst region
    exact pre.separation a ha (work_substack pre hb)
  have localAddress (offset : Nat) (bound : offset ≤ 680) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) := by
    rw [← show stackPtr s = scratch initial from current.rsp]
    exact ScalarFrame.scalar_stack_address current.rsp (by decide) bound
  have keep : ∀ offset ∈ ([64,72,80,424] : List Nat), ∀ i < 8,
      t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro offset member i hi
    have bound : offset ≤ 424 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    rw [localAddress offset (by omega)]
    exact result.preserved (680-offset) 8 (by omega) (by omega) (.inl (by
      change 248 + 8 ≤ 680 - offset
      omega)) i hi
  have context := current.toContext.of_copied result.toFrameState drbg
    ((result.calleeSaved .rbp (by simp)).trans current.descriptors) keep
  have hmac : HMAC.HmacStateAt t (scratch initial + 432) state.key input := by
    apply current.hmac.copy
    simpa only [BitVec.ofNat_eq_ofNat, sourceAddress, destinationAddress, copyLayout] using result.copied
  obtain ⟨fuel, run⟩ := result.execution
  exact ⟨fuel, t, run, context, result.rip,
    (result.calleeSaved .rbx (by simp)).trans current.hashPointer, hmac⟩

end P256.Proofs.Nonce.Update.Zero
