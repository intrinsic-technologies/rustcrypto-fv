import P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize.Payload
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize.Frame
import P256.Proofs.Signing.Wrapper.Hash.Finalize.State


set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pre [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (input : HashEntry initial start secret message)
    (state : Compressed initial start s message) : Pre s := by
  refine ⟨state.rip, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i.toNat + 4 ≤ 520 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      stack_readable input.context state.toFrame
        (offset := i.toNat) bound
  · intro i hi
    have bound : i.toNat + 4 ≤ 520 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      stack_writable input.context state.toFrame
        (offset := i.toNat) bound (by decide)
  · intro i hi offset len hcode
    have bound : i.toNat + 4 ≤ 520 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, rspOf, stackPtr, Operand.read_reg64] using
      stack_code input.context state.toFrame
        (offset := i.toNat) bound hcode

theorem correct [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (input : HashEntry initial start secret message)
    (state : Compressed initial start s message) :
    ∃ t, Result initial start t message := by
  obtain ⟨fuel, t, execution, ready, _, result⟩ := run (returnBoundary initial) (outside input.context) s
    (readyToStep state.machine state.bindingsSupported) (code state.loaded) (pre input state)
  have address : rspOf s + 0 = stackPtr initial - 520 := by
    change stackPtr s + 0#64 = stackPtr initial - 520#64
    simpa only [BitVec.add_zero] using state.rsp
  have bounds := stack_bounds (stack input.context)
  have destination : (rspOf s + 0).toNat = (stackPtr initial).toNat - 520 := by
    rw [address]
    exact stack_sub_toNat (stack input.context) (by decide)
  have writes : WritesWithin (effect s).components #v[workRegion initial] := by
    apply writesWithin
    · change (stackPtr initial).toNat - 5112 + (5112 - 240) < 2^32
      omega
    · rw [destination]
      change (stackPtr initial).toNat - 5112 ≤ (stackPtr initial).toNat - 520
      omega
    · rw [destination]
      change (stackPtr initial).toNat - 520 + 32 ≤
        (stackPtr initial).toNat - 5112 + (5112 - 240)
      omega
  have frame := state.toFrame.after_effect input.context execution ready result.agrees writes
    ((register_frame result (r := 4) (by decide)).trans state.rsp)
    (by simp [effect, Effect.components, Write.component, Operand.component])
  refine ⟨t, frame, result.rip, ?_⟩
  obtain ⟨hash, hashAt, digest⟩ := state.hash
  have sp : rspOf s = frameBase initial := state.rsp
  rw [← sp] at hashAt
  have bytes := payload (pre input state) hashAt result
  simpa only [sp, digest] using bytes

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize
