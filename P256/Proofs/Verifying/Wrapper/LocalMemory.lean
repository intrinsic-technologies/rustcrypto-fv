import P256.Proofs.Verifying.Wrapper.WorkState
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ReturnState.local_readable [Bindings] {initial s : RamState}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280) {offset len : Nat}
    (bound : offset+len ≤ 280) : MemReadable s (stackPtr s+BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega)]
  exact readable_of_grow (stack_sub_readable stack (by omega) (by omega)) state.allocated

theorem ReturnState.local_writable [Bindings] {initial s : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (state : ReturnState initial s)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    {offset len : Nat} (bound : offset+len ≤ 240) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s+BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega)]
  exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) state.allocated
    (by change 280-offset ≤ 10280; omega) (by omega) positive

theorem ReturnState.local_code [Bindings] {initial s : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (state : ReturnState initial s)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    {offset len codeOffset codeLen : Nat} (bound : offset+len ≤ 240)
    (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr s+BitVec.ofNat 64 offset) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega)]
  intro i hi j hj he
  apply call_stack_avoids call
    (stackPtr initial-BitVec.ofNat 64 (280-offset)+BitVec.ofNat 64 i) ?_ (.inl ?_)
  · exact stack_buffer_contains call.stackAvailable.1
      (by change 280-offset ≤ 10280; omega) (by omega)
      (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1
        (offset := 280-offset) (len := len) (by change 280-offset ≤ 10280; omega) (by omega))
        (Nat.le_refl _) (Nat.le_refl _) hi)
  · rw [he,BitVec.add_assoc,← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

theorem ReturnState.local_work [Bindings] {initial s : RamState}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280)
    {offset len : Nat} {a : BitVec 64} (bound : offset+len ≤ 240)
    (covered : (Component.mem (stackPtr s+BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega)] at covered
  exact work_contains stack (by omega) (by omega) covered

end P256.Proofs.Verifying.Wrapper
