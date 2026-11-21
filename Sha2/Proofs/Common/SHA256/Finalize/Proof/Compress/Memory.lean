import Sha2.Proofs.Common.SHA256.Finalize.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def Writes (L : Layout) (sp : BitVec 64) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (Component.mem (L.buffer sp) 64).Covers a ∨
    (Component.mem (L.scratch sp) 64).Covers a

theorem writes_within [Bindings] {L : Layout} {initial : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {components : List Component}
    (ctx : Context L initial regions reserve) (writes : Writes L (L.sp initial) components) :
    WritesWithin components (footprint L (L.sp initial)) := by
  intro c hc a ha
  rcases writes c hc a ha with low | high
  · refine ⟨⟨(L.buffer (L.sp initial)).toNat, 64⟩, by simp [footprint], ?_⟩
    exact ctx.local_cover (base := L.variant.buffer.value) (offset := 0)
      (by have := ctx.wf.bufferFits; omega) (by decide) low
  · refine ⟨⟨(L.scratch (L.sp initial)).toNat, 64⟩, by simp [footprint], ?_⟩
    exact ctx.local_cover (base := L.variant.scratch) (offset := 0)
      ctx.wf.scratchFits (by decide) high

theorem hash_bytes {L : Layout} {sp : BitVec 64} {s t : RamState}
    {components : List Component} (frame : AgreesExcept components s t)
    (writes : Writes L sp components) :
    ∀ i < 32, t.external[L.hash sp + BitVec.ofNat 64 i]? =
      s.external[L.hash sp + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covered
  rcases writes c hc _ covered with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · have apart : OffsetsApart (BitVec.ofNat 64 L.variant.buffer.value) 64
        (BitVec.ofNat 64 (L.variant.buffer.value+64)) 32 := by
      cases L.variant <;> unfold OffsetsApart <;> decide +kernel
    apply apart.ne sp hj hi (by decide)
    simpa only [Layout.hash, Layout.buffer, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using he.symm
  · have apart : OffsetsApart (BitVec.ofNat 64 L.variant.scratch) 64
        (BitVec.ofNat 64 (L.variant.buffer.value+64)) 32 := by
      cases L.variant <;> unfold OffsetsApart <;> decide +kernel
    apply apart.ne sp hj hi (by decide)
    simpa only [Layout.hash, Layout.buffer, Layout.scratch, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using he.symm

theorem preserve [Bindings] {L : Layout} {initial before s t : RamState}
    {n reserve fuel : Nat} {regions : Vector MemoryRegion n} {hash : Array UInt32}
    {components : List Component} (ctx : Context L initial regions reserve)
    (input : HashAt L initial before s regions hash)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : Writes L (L.sp initial) components)
    (regs : ∀ r : BitVec 5, r ≠ 0 → r ≠ 1 → .reg r ∉ components)
    (df : .df ∉ components) : HashAt L initial before t regions hash := by
  refine ⟨input.toPreserved.of_agrees ctx run ready frame (writes_within ctx writes) ?_ df,
    Sha2.Proofs.Wrapper.hashState_of_bytes input.hashWords (hash_bytes frame writes), ?_⟩
  · intro r small kept
    apply regs r
    all_goals
      intro eq
      apply kept
      simp [eq, Variant.clobbered]
  · intro notFirst
    exact (frame.read (n := 64) (r := L.variant.hashReg) (regs _
      (by cases L.variant <;> decide) (by cases L.variant <;> decide))).trans (input.hashPointer notFirst)

theorem scratch_cover {L : Layout} {sp : BitVec 64} {offset len : Nat}
    (bound : offset + len ≤ 64) {a : BitVec 64}
    (covered : (Component.mem (sp + BitVec.ofNat 64 (L.variant.scratch+offset)) len).Covers a) :
    (Component.mem (L.scratch sp) 64).Covers a := by
  obtain ⟨i, hi, rfl⟩ := covered
  refine ⟨offset+i, by omega, ?_⟩
  simp only [Layout.scratch, BitVec.ofNat_add, BitVec.add_assoc]

theorem buffer_cover {L : Layout} {sp : BitVec 64} {offset len : Nat}
    (bound : offset + len ≤ 64) {a : BitVec 64}
    (covered : (Component.mem (sp + BitVec.ofNat 64 (L.variant.buffer.value+offset)) len).Covers a) :
    (Component.mem (L.buffer sp) 64).Covers a := by
  obtain ⟨i, hi, rfl⟩ := covered
  refine ⟨offset+i, by omega, ?_⟩
  simp only [Layout.buffer, BitVec.ofNat_add, BitVec.add_assoc]

theorem scratch_keeps_buffer {L : Layout} {sp : BitVec 64} {s t : RamState}
    {components : List Component} (frame : AgreesExcept components s t)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a → (Component.mem (L.scratch sp) 64).Covers a) :
    ∀ i < 64, t.external[L.buffer sp + BitVec.ofNat 64 i]? =
      s.external[L.buffer sp + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covered
  obtain ⟨j, hj, he⟩ := writes c hc _ covered
  have apart : OffsetsApart (BitVec.ofNat 64 L.variant.scratch) 64
      (BitVec.ofNat 64 L.variant.buffer.value) 64 := by
    cases L.variant <;> unfold OffsetsApart <;> decide +kernel
  apply apart.ne sp hj hi (by decide)
  simpa only [Layout.buffer, Layout.scratch] using he.symm

end Sha2.Proofs.Common.SHA256.Finalize.Compress
