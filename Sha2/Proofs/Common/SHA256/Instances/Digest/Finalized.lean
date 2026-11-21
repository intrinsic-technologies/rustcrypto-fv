import Sha2.Proofs.Common.SHA256.Instances.Digest.Entry
import Sha2.Proofs.Common.SHA256.Instances.Finalize
import Sha2.Proofs.Common.SHA256.Finalize.Correctness
import Sha2.Proofs.Common.SHA256.Blocks.Finalize

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem finalized [bindings : Bindings] {initial s : RamState} {data : ByteArray} {v : Wrapper.Variant}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (state : ExecutionState initial s (regions initial v))
    (prepared : Finalize.Prepared (Finalization.digest.layout v)
      ((Finalization.digest.layout v).sp initial) data s) :
    ∃ t, Finalize.Finalized (Finalization.digest.layout v) initial s t (regions initial v) data := by
  have avoid : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have within : ∀ region ∈ Finalize.footprint (Finalization.digest.layout v)
      ((Finalization.digest.layout v).sp initial),
      ∀ a, region.Contains a → ∃ outer ∈ regions initial v, outer.Contains a := by
    intro region member a ha
    change region ∈ #v[⟨(stackPtr initial - 312 + 0).toNat, 64⟩,
      ⟨(stackPtr initial - 312 + 0 + 64).toNat, 32⟩,
      ⟨(stackPtr initial - 312 + 104).toNat, 64⟩,
      ⟨(stackPtr initial - 312 - 344).toNat, 344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    refine ⟨Stack.region initial 784, by simp [regions], ?_⟩
    rcases member with rfl | rfl | rfl | rfl
    · exact stack_frame_region_subset call.stack (frame := 312) (offset := 0)
        (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · have zero : stackPtr initial - 312 + 0 = stackPtr initial - 312 := BitVec.add_zero _
      rw [zero] at ha
      exact stack_frame_region_subset call.stack (frame := 312) (offset := 64)
        (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · exact stack_frame_region_subset call.stack (frame := 312) (offset := 104)
        (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · have sub : stackPtr initial - 312 - 344 = stackPtr initial - BitVec.ofNat 64 656 := by
        rw [BitVec.sub_sub]; rfl
      rw [sub] at ha
      exact stack_sub_region_subset call.stack (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
  exact Finalize.correct (Finalization.digest.layout v) (Finalization.wellFormed .digest (v := v))
    (Finalization.flow .digest (v := v)) (Finalization.codeFacts .digest (v := v))
    (Finalize.blockContracts _ _
      (valid_return_boundary machine call.stack call.returnAddress).2.2
      (Finalization.flow .digest (v := v)) (Finalization.codeFacts .digest (v := v)))
    stride machine call.stack avoid call.returnAddress state prepared within

end Sha2.Proofs.Common.SHA256.Instances.Digest
