import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.State
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem text_range {offset len : Nat} (h : offset + len ≤ 118431) :
    ∀ i < len, InProgram ((Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i) := by
  intro i hi
  rw [add_ofNat_add_ofNat]
  exact P256.Proofs.Program.inProgram_of_textOffset (offset + i) (by omega)

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem stack_contains (pre : BinaryFieldPre s boundary 0x114380 128)
    {offset len i : Nat} (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8) (hi : i < len) :
    (Stack.region s 128).Contains (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  apply P256.Proofs.Program.memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [P256.Proofs.Program.stack_sub_toNat pre.stack hoffset]
    change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - offset
    omega
  · rw [P256.Proofs.Program.stack_region_end, P256.Proofs.Program.stack_sub_toNat pre.stack hoffset]
    have := (P256.Proofs.Program.stack_bounds pre.stack).1
    omega

theorem stack_codeApart (pre : BinaryFieldPre s boundary 0x114380 128)
    {offset len codeLen : Nat} {p : BitVec 64}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8)
    (hc : ∀ i < codeLen, InProgram (p + BitVec.ofNat 64 i)) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len p codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 128) (by simp) _
    (stack_contains pre hoffset hlen hi) (.inl _)
  rw [he]
  exact hc j hj

theorem SavedState.stack_readable (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : SavedState s t) {offset len : Nat}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8) :
    MemReadable t (stackPtr s - BitVec.ofNat 64 offset) len :=
  P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack hoffset hlen)
    state.allocated

theorem SavedState.stack_writable8 (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : SavedState s t) {offset : Nat} (hoffset : offset ≤ 128) (halign : offset % 8 = 0) :
    MemWritable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
  P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) hoffset halign)
    state.allocated

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
