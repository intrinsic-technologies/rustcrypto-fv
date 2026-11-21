import P256.Proofs.Signing.Wrapper.State
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.HashCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem local_readable [Bindings] {initial s : RamState}
    (state : State initial s 520) (stack : Stack.Valid initial 5112) {offset len : Nat}
    (bound : offset+len ≤ 520) : MemReadable s (stackPtr s+BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) state.rsp (by decide) (by omega)]
  exact readable_of_grow (stack_sub_readable stack (by omega) (by omega)) state.allocated

theorem local_writable [Bindings] {initial s : RamState}
    {secret message : ByteArray} {slices : Array Input}
    (state : State initial s 520)
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    {offset len : Nat} (bound : offset+len ≤ 472) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s+BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) state.rsp (by decide) (by omega)]
  exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) state.allocated
    (by change 520-offset ≤ 5112; omega) (by omega) positive

theorem local_code [Bindings] {initial s : RamState}
    {secret message : ByteArray} {slices : Array Input}
    (state : State initial s 520)
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    {offset len codeOffset codeLen : Nat} (bound : offset+len ≤ 472)
    (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr s+BitVec.ofNat 64 offset) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) state.rsp (by decide) (by omega)]
  intro i hi j hj he
  apply call_stack_avoids call
    (stackPtr initial-BitVec.ofNat 64 (520-offset)+BitVec.ofNat 64 i) ?_ (.inl ?_)
  · exact stack_buffer_contains call.stackAvailable.1
      (by change 520-offset ≤ 5112; omega) (by omega)
      (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1
        (offset := 520-offset) (len := len) (by change 520-offset ≤ 5112; omega) (by omega))
        (Nat.le_refl _) (Nat.le_refl _) hi)
  · rw [he,BitVec.add_assoc,← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

theorem local_work [Bindings] {initial s : RamState}
    (state : State initial s 520) (stack : Stack.Valid initial 5112)
    {offset len : Nat} {a : BitVec 64} (bound : offset+len ≤ 472)
    (covered : (Component.mem (stackPtr s+BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) state.rsp (by decide) (by omega)] at covered
  exact work_contains stack (by omega) (by omega) covered

theorem after_registers [Bindings] {initial s t : RamState} {secret message : ByteArray}
    {slices : Array Input} {offset fuel : Nat} {cs : List Component}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s offset) (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (noMemory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : Component.reg 4 ∉ cs)
    (df : Component.df ∉ cs) :
    State initial t offset :=
  state.after_effect call run ready agrees
    (by intro c hc a ha; exact (noMemory c hc a ha).elim)
    ((agrees.read (n := 64) sp).trans state.rsp) df

end P256.Proofs.Signing.Wrapper.Entry.HashCall
