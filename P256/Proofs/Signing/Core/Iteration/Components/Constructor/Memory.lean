import P256.Proofs.Signing.Core.Iteration.Components.Constructor.State
import P256.Proofs.Program.ScalarFrame.Work

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev workRegion (s : RamState) : MemoryRegion := ScalarFrame.Work.region s 512 24

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    {offset len : Nat} (bound : offset + len ≤ 216) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    {offset len : Nat} (bound : offset + len ≤ 216) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (stackPtr t + BitVec.ofNat 64 offset) len := by
  have readable := stack_readable pre state bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi hreserved
  apply pre.avoids (Stack.region s 512) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  rw [ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)]
  exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 216)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 512) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)]
    exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩
  · apply Or.inl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset+j) (by omega)

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
