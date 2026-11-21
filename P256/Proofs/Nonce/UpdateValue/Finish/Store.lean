import P256.Proofs.Nonce.UpdateValue.Finish.StorePre
import P256.Proofs.Nonce.UpdateValue.Finish.StoreMemory
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Nonce.UpdateValue.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem store [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}
    (pre : UpdateValuePre initial boundary state) (input : Finalized initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState initial t ∧ t.RIP = 0x10ac19 ∧
      DrbgAt t (initial.regValue .rdi) (updateValue state) := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := store_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0xabe2 storeBytes
      (by decide) (by decide +kernel)) (store_pre pre input)
  have frame := store_frame pre input ready effect
  have pointer : valuePointer s = initial.regValue .rdi + 32#64 := input.valuePointer
  have rsp : stackPtr s = scratch initial := input.rsp
  have words : ∀ j < 4,
      memLoad t.external (initial.regValue .rdi + 32#64 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (scratch initial + 8#64 + BitVec.ofNat 64 (8*j)) 64 := by
    have h := effect.writes
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
      memLoad t.external (valuePointer s + 24) 64 = memLoad s.external (stackPtr s + 32) 64 ∧
      memLoad t.external (valuePointer s + 16) 64 = memLoad s.external (stackPtr s + 24) 64 ∧
      memLoad t.external (valuePointer s + 8) 64 = memLoad s.external (stackPtr s + 16) 64 ∧
      memLoad t.external (valuePointer s + 0) 64 = memLoad s.external (stackPtr s + 8) 64 at h
    rw [pointer, rsp] at h
    have h := h.2.2.2.2.2.2.2.2
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [BitVec.add_assoc] using h.2.2.2
    · simpa [BitVec.add_assoc] using h.2.2.1
    · simpa [BitVec.add_assoc] using h.2.1
    · simpa [BitVec.add_assoc] using h.1
  have digest : (MemoryRegion.mk (initial.regValue .rdi + 32#64).toNat 32).HasBytes t.external
      (Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key state.value) := by
    apply hasBytes_copy input.output
    apply HMAC.Key.Output.bytes_of_words (count := 4)
    · have h := ScalarFrame.stack_readable pre.callee input.toFrameState (offset := 8) (len := 32)
        (by decide) (by decide)
      have sp : stackPtr s = scratch initial := input.rsp
      simpa only [sp, BitVec.ofNat_eq_ofNat, Nat.reduceMul] using h
    · exact state_readable pre frame (offset := 32) (len := 32) (by decide)
    · exact words
  refine ⟨fuel, t, run, frame, effect.rip, ?_⟩
  dsimp only [DrbgAt, updateValue]
  exact ⟨store_key (state := state) pre input effect, digest⟩

end P256.Proofs.Nonce.UpdateValue.Finish
