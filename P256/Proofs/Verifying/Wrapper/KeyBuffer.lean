import P256.Proofs.Verifying.Wrapper.Guarded
import P256.Proofs.Verifying.Wrapper.KeyCopy.Memory
import P256.Proofs.Program.WrapperFirstInput
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem key_buffer_pre [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (state : KeyReady initial s key) : KeyCopy.Pre 0x103088 s := by
  have sp : stackPtr s = stackPtr initial-280#64 := state.rsp
  have readable := hasBytes_memReadable state.bounded state.bytes
  have bounded : (MemoryRegion.mk (stackPtr s).toNat 65).Bounded := by
    rw [state.rsp]
    exact stack_buffer_bounded call.stackAvailable.1 (by decide) (by decide)
  have within {i : Nat} (hi : i < 65) :
      (callStack verifyingKeyVerify initial).Contains (stackPtr s + BitVec.ofNat 64 i).toNat := by
    apply stack_contains_callStack
    apply stack_buffer_contains call.stackAvailable.1 (by decide : 280 ≤ verifyingKeyVerify.minStackBytes)
      (by decide : 65 ≤ 280+8)
    rw [← sp]
    exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
  have sep := wrapper_read_disjoint call (first_input_region call)
    (callStack verifyingKeyVerify initial) (by simp [wrapperRegions])
  refine ⟨state.rip, ?_, ?_, ?_, ?_⟩
  · intro off len bound
    refine ⟨?_, ?_⟩
    · have low := readable.low
      rw [state.keySize] at low
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · intro i hi
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using readable.mem (off+i) (by
        rw [state.keySize]
        omega)
  · rw [state.rsp]
    exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) state.allocated
      (by decide) (by decide) (by decide)
  · intro i hi j hj he
    apply sep (s.regValue .rdx + BitVec.ofNat 64 j).toNat
    · rw [← state.source]
      apply memoryRegion_contains_add state.bounded (len := 65) (Nat.le_refl _) _ hj
      change (s.regValue .rdx).toNat + 65 ≤ (s.regValue .rdx).toNat + key.size
      rw [state.keySize]
      exact Nat.le_refl _
    · rw [← he]
      exact within hi
  · intro off len bound offset codeLen codeBound i hi j hj he
    apply call_stack_avoids call (stackPtr s + BitVec.ofNat 64 off + BitVec.ofNat 64 i) ?_ (.inl ?_)
    · apply stack_buffer_contains call.stackAvailable.1 (by decide : 280 ≤ verifyingKeyVerify.minStackBytes)
        (by decide : 65 ≤ 280+8)
      rw [← sp]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (show off+i < 65 by omega))
    · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (offset+j) (by omega)

end P256.Proofs.Verifying.Wrapper
