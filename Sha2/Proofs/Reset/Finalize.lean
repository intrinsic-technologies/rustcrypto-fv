import Sha2.Proofs.Reset.Entry
import Sha2.Proofs.Common.SHA256.Instances.Finalize
import Sha2.Proofs.Common.SHA256.Finalize.Correctness
import Sha2.Proofs.Common.SHA256.Blocks.Finalize

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances

theorem finalized [bindings : Bindings] {routine : Routine} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (v : Wrapper.Variant) (occ : Finalization)
    (stackSize : routine.minStackBytes = occ.reserve)
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (prepared : Finalize.Prepared (occ.layout v) ((occ.layout v).sp initial) message s) :
    ∃ t, Finalize.Finalized (occ.layout v) initial s t (regions routine initial) message := by
  have stack : Stack.Valid initial occ.reserve := by
    simpa only [stackSize] using call.stack
  have avoid : (Stack.region initial occ.reserve).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    rw [← stackSize]
    exact (call.separation.2 _ (by simp)).2
  have within : ∀ region ∈ Finalize.footprint (occ.layout v) ((occ.layout v).sp initial),
      ∀ a, region.Contains a → ∃ outer ∈ regions routine initial, outer.Contains a := by
    intro region member address inside
    refine ⟨Stack.region initial occ.reserve, ?_, ?_⟩
    · simp [regions, stackSize]
    · exact Finalize.footprint_subset_stack (occ.wellFormed (v := v)) stack
        region member address inside
  exact Finalize.correct (occ.layout v) (occ.wellFormed (v := v)) (occ.flow (v := v))
    (occ.codeFacts (v := v))
    (Finalize.blockContracts _ _
      (valid_return_boundary machine stack call.returnAddress).2.2
      (occ.flow (v := v)) (occ.codeFacts (v := v)))
    stride machine stack avoid call.returnAddress state prepared within

end Sha2.Proofs.Reset
