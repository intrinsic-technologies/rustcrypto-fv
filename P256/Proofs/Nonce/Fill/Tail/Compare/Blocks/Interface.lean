import P256.Proofs.Nonce.Fill.Tail.Compare.Frame
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure BlockPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ offset : Nat, offset + 8 ≤ 232 → offset % 8 = 0 →
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
  order : ∀ offset : Nat, offset + 8 ≤ 32 → offset % 8 = 0 →
    MemReadable s (s.regValue .r15 + BitVec.ofNat 64 offset) 8
  apart : ∀ offset len : Nat, offset + len ≤ 232 → ∀ codeOffset codeLen : Nat,
    codeOffset + codeLen ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

theorem block_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress p : BitVec 64} {original state : Nonce.State}
    (pre : Fill.Pre initial boundary orderAddress original)
    (input : Context initial s orderAddress state) (rip : s.RIP = p) : BlockPre p s := by
  refine ⟨rip, fun offset bound aligned => stack_writable8 pre input.toFrame (by omega) aligned,
    ?_, fun offset len bound codeOffset codeLen codeBound => stack_code pre input.toFrame bound codeBound⟩
  intro offset bound aligned
  rw [input.r15]
  have address : (orderAddress + BitVec.ofNat 64 offset).toNat = orderAddress.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64)]
    exact Nat.mod_eq_of_lt (by have hb : orderAddress.toNat + 32 < 2^32 := pre.orderBounded; omega)
  refine ⟨?_, ?_⟩
  · rw [address]
    have hb : orderAddress.toNat + 32 < 2^32 := pre.orderBounded
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply input.allocated
    exact Option.isSome_iff_exists.mpr (pre.orderAllocated _
      (memoryRegion_contains_add pre.orderBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : offset+i < 32)))

end P256.Proofs.Nonce.Fill.Tail.Compare.Blocks
