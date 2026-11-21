import Sha2.Proofs.Wrapper.Hash.Finalize.State
import Sha2.Proofs.Wrapper.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def Writes (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (Component.mem (stackPtr initial - 344) 64).Covers a ∨
    (Component.mem (stackPtr initial - 240) 64).Covers a

theorem writes_mem {initial s : RamState} {offset len : Nat}
    (rsp : stackPtr s = stackPtr initial - 344)
    (bounds : offset + len ≤ 64 ∨ 104 ≤ offset ∧ offset + len ≤ 168) :
    ∀ a, (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Covers a →
      (Component.mem (stackPtr initial - 344) 64).Covers a ∨
      (Component.mem (stackPtr initial - 240) 64).Covers a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := ha
  change rspOf s = stackPtr initial - 344 at rsp
  rcases bounds with low | high
  · left
    refine ⟨offset+i, by omega, ?_⟩
    rw [rsp, BitVec.ofNat_add, BitVec.add_assoc]
  · right
    refine ⟨offset-104+i, by omega, ?_⟩
    rw [rsp, BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le offset 104 (by omega) high.1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (BitVec.ofNat 64 offset),
      BitVec.add_comm (BitVec.ofNat 64 offset) (-104#64),
      BitVec.add_assoc (-104#64), ← BitVec.add_assoc (-240)]
    rfl

theorem kept_bytes {initial s t : RamState} {components : List Component} {offset len : Nat}
    (frame : AgreesExcept components s t) (writes : Writes initial components)
    (first : OffsetsApart (-344) 64 (-(BitVec.ofNat 64 offset)) len)
    (second : OffsetsApart (-240) 64 (-(BitVec.ofNat 64 offset)) len)
    (bound : 64 + len < 2^64) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covers
  rcases writes c hc _ covers with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · apply OffsetsApart.ne first (stackPtr initial) hj hi bound
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  · apply OffsetsApart.ne second (stackPtr initial) hj hi bound
    simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem preserve [Bindings] {initial s t : RamState} {inputs : Array Input}
    {hash : Array UInt32} {fuel : Nat} {components : List Component}
    (ctx : Context initial inputs v) (input : HashAt initial s hash v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : Writes initial components)
    (regs : ∀ r ∈ ([4,14] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp) :
    HashAt initial t hash v := by
  have localWrites : Wrapper.LocalWrites initial components := by
    intro c hc a ha
    rcases writes c hc a ha with low | high
    · exact Wrapper.local_memory (offset := 344) (len := 64)
        (by decide) (by decide) (.inl (by decide)) a low
    · exact Wrapper.local_memory (offset := 240) (len := 64)
        (by decide) (by decide) (.inl (by decide)) a high
  refine ⟨Wrapper.preserved_of_agrees ctx input.toPreserved run ready frame localWrites
    (regs 4 (by simp)) hdf, ?_, ?_⟩
  · exact Wrapper.hashState_of_bytes input.hashWords (kept_bytes frame writes
      (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide))
  · exact (frame.read (n := 64) (regs 14 (by simp))).trans input.hashPointer

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
