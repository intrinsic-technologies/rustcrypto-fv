import Sha1.Proofs.Streaming.UpdateFinalize.Geometry
import Sha1.Proofs.Buffered.Finalize.Digest.Prepare

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Streaming.UpdateFinalize Sha1.Proofs.Buffered

variable [bindings : Bindings] {initial s t : RamState} {inputs : Array Slices.Input}
  {message : ByteArray}

private theorem finalize_covers (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    {c : Component} {a : BitVec 64} (hm : c ∈ Finalize.Kind.changes .updateFinalizeCopy s)
    (ha : c.Covers a) :
    (Finalize.Kind.stackRegion .updateFinalizeCopy s).Contains a.toNat ∨
      (SliceHash.outputRegion SliceHash.updateFinalize initial).Contains a.toNat := by
  cases c with
  | mem addr len =>
    simp only [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges,
      Finalize.Kind.stackBytes, List.map, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, reduceCtorEq, false_or, Component.mem.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ((hf.finalize_storage hc).localCover ha)
    · right
      apply DigestPrepare.contains_of_mem_covers hc.outputInMemory.2.1
      change Component.Covers (.mem (BitVec.ofNat 64 (initial.regValue .rcx).toNat) 20) a
      have hptr : (Operand.mem (stackPtr s + 0xc0) : Operand 64).read s = initial.regValue .rcx :=
        hf.output
      rw [hptr] at ha
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ha
  | _ => exact absurd ha (by simp [Component.Covers])

theorem finalize_saved_word (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hp : Finalize.Post .updateFinalizeCopy (returnBoundary initial) message s t)
    (k : Nat) (hk : 312 ≤ k) (he : k + 8 ≤ 368) : stackWord t k = stackWord s k := by
  obtain ⟨hl, _, hh, _⟩ := hf.stack_bounds hc.stackAvailable
  unfold stackWord
  rw [hp.rsp]
  apply Finalize.Digest.read_of_agrees hp.agrees
  intro i hi c hmem hcov
  obtain h | h := finalize_covers hf hc hmem hcov
  all_goals
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)] at h
  · change (stackPtr s).toNat - 344 ≤ _ ∧ _ < (stackPtr s).toNat - 344 + 656 at h
    omega
  · apply hc.separation.1 _ h
    apply (hf.stack_contains hc.stackAvailable).mpr
    constructor <;> omega

theorem finalize_write_frame (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hp : Finalize.Post .updateFinalizeCopy (returnBoundary initial) message s t) :
    MemoryWriteFrame initial t #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
      Stack.region initial SliceHash.updateFinalize.minStackBytes] := by
  apply memoryWriteFrame_trans (t := s)
  · intro a ha
    apply hf.memory
    intro r hr
    simp only [Vector.mem_mk, Array.mem_singleton] at hr
    exact hr ▸ ha _ (Vector.getElem_mem (i := 1) (by decide))
  · apply hp.agrees.memoryWriteFrame
    intro c hm a hx
    obtain h | h := finalize_covers hf hc hm hx
    · exact ⟨_, Vector.getElem_mem (i := 1) (by decide), hf.finalize_stack_subset hc.stackAvailable h⟩
    · exact ⟨_, Vector.getElem_mem (i := 0) (by decide), h⟩

theorem finalize_stack_readable (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hp : Finalize.Post .updateFinalizeCopy (returnBoundary initial) message s t) :
    MemReadable t (stackPtr t) 368 := by
  obtain ⟨hl, _, hh, _⟩ := hf.stack_bounds hc.stackAvailable
  rw [hp.rsp]
  refine ⟨by omega, ?_⟩
  intro i hi
  apply hp.agrees.grow
  apply hf.grows
  apply Option.isSome_iff_exists.mpr
  apply hc.stackAvailable.2.1
  rw [hf.stack_contains hc.stackAvailable, toNat_add_ofNat _ _ (by omega)]
  constructor <;> omega

end Sha1.Proofs.Entry.UpdateFinalize
