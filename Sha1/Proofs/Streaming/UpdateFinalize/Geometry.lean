import Sha1.Proofs.Streaming.Invariant
import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Buffered.DigestPrepare.Geometry

namespace Sha1.Proofs.Streaming.UpdateFinalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered

variable [bindings : Bindings] {initial s : RamState} {inputs : Array Slices.Input}

theorem Frame.stack_bounds (h : Frame initial s) (hs : Stack.Valid initial SliceHash.updateFinalize.minStackBytes) :
    344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 360 = (stackPtr initial).toNat ∧
    (stackPtr s).toNat + 368 < 2^32 ∧ (stackPtr s).toNat % 16 = 0 := by
  obtain ⟨hb, _, hl, ha⟩ := hs
  change 704 ≤ (stackPtr initial).toNat at hl
  change (stackPtr initial).toNat - 704 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 704)) < 2^32 at hb
  change (stackPtr initial).toNat % 16 = 8 at ha
  have hr : (stackPtr s).toNat = (stackPtr initial).toNat - 360 := by
    rw [h.stack, BitVec.toNat_sub_of_le]
    · rfl
    · change 360 ≤ (stackPtr initial).toNat
      omega
  omega

theorem Frame.stack_contains (h : Frame initial s)
    (hs : Stack.Valid initial SliceHash.updateFinalize.minStackBytes) {a : Nat} :
    (Stack.region initial SliceHash.updateFinalize.minStackBytes).Contains a ↔
      (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat + 368 := by
  obtain ⟨_, hr, _, _⟩ := h.stack_bounds hs
  change ((stackPtr initial).toNat - 704 ≤ a ∧ a < (stackPtr initial).toNat - 704 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 704))) ↔ _
  omega

theorem Frame.finalize_stack_subset (h : Frame initial s)
    (hs : Stack.Valid initial SliceHash.updateFinalize.minStackBytes) {a : Nat}
    (ha : (Finalize.Kind.stackRegion .updateFinalizeCopy s).Contains a) :
    (Stack.region initial SliceHash.updateFinalize.minStackBytes).Contains a := by
  apply (h.stack_contains hs).mpr
  change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 656 at ha
  have hl := (h.stack_bounds hs).1
  omega

theorem Frame.finalize_storage (h : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs) :
    Finalize.Storage .updateFinalizeCopy s := by
  obtain ⟨hl, _, hh, ha⟩ := h.stack_bounds hc.stackAvailable
  refine ⟨hl, ?_, ha, ?_, ?_⟩
  · change (stackPtr s).toNat + 312 < 2^32
    omega
  · intro a hin
    exact Option.isSome_iff_exists.mp (h.grows a (Option.isSome_iff_exists.mpr
      (hc.stackAvailable.2.1 a (h.finalize_stack_subset hc.stackAvailable hin))))
  · intro a hin
    exact (hc.separation.2 _ (Vector.getElem_mem (i := 1) (by decide))).2 a
      (h.finalize_stack_subset hc.stackAvailable hin)

theorem Frame.finalize_output (h : Frame initial s) :
    Finalize.Kind.resultRegion .updateFinalizeCopy s =
      SliceHash.outputRegion SliceHash.updateFinalize initial := by
  exact congrArg (fun (p : BitVec 64) ↦ (⟨p.toNat, 20⟩ : MemoryRegion)) h.output

end Sha1.Proofs.Streaming.UpdateFinalize
