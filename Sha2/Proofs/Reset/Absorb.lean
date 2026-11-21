import Sha2.Proofs.Reset.DispatchState
import Sha2.Proofs.Common.SHA256.Absorb.Correctness
import Sha2.Proofs.Common.SHA256.Absorb.Traversal
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Contracts

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Absorb Sha2.Proofs.Common.SHA256.Instances.Absorption

theorem discarded [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (blocks : Absorb.BlockContracts (resetDiscarded v).chunk (returnBoundary initial)) :
    ∃ p h u s,
      (Prologue.effect (resetRoutine v).entryAddress .six200 initial).Holds initial p ∧
      (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h ∧
      Initialize.Post (Instances.Initialization.resetInitial.layout v) (rspOf h) h u ∧
      ((inputs.size = 0 ∧ ExecutionState initial s (regions (resetRoutine v) initial) ∧
        s.RIP = Dispatch.entry v + 608#64 ∧
        stackPtr s = (resetDiscarded v).chunk.sp initial ∧
        HasherAt s ((resetDiscarded v).chunk.sp initial) ByteArray.empty v.initialHash ∧
        AgreesExcept [.flags, .rip] u s) ∨
       (0 < inputs.size ∧ ∃ t, Table.Finished (resetDiscarded v) initial s t (regions (resetRoutine v) initial) inputs ∧
        memLoad s.external ((resetDiscarded v).chunk.sp initial + 184#64) 64 =
          initial.regValue .rcx ∧
        AgreesExcept [.mem (rspOf u + 184#64) 8, .reg 15#5, .flags, .rip] u s)) := by
  obtain ⟨p, h, u, s, push, header, init, state, data, separation, branch⟩ := dispatched v machine call
  refine ⟨p, h, u, s, push, header, init, ?_⟩
  rcases branch with ⟨empty, rip, rsp, hasher, frame⟩ | ⟨loop, output, frame⟩
  · exact Or.inl ⟨empty, state, rip, rsp, hasher, frame⟩
  · have stack : Stack.Valid initial 720 := by simpa only [resetRoutine_stack] using call.stack
    have avoid : (Stack.region initial 720).Avoids
        (fun a => InProgram a ∨ InPageTables a) := by
      simpa only [resetRoutine_stack, InPageTables] using (call.separation.2 _ (by simp [resetRoutine_stack])).2
    have count : Table.CountAt (resetDiscarded v) ((resetDiscarded v).chunk.sp initial) s := by
      constructor
      intro offset impossible
      cases impossible
    have within : ∀ region ∈ Table.footprint (resetDiscarded v) ((resetDiscarded v).chunk.sp initial),
        ∀ a, region.Contains a → ∃ outer ∈ regions (resetRoutine v) initial, outer.Contains a := by
      intro region member address inside
      refine ⟨Stack.region initial 720, by simp [regions, resetRoutine_stack], ?_⟩
      exact Table.footprint_subset_stack (resetDiscarded_wellFormed v) stack region member address inside
    obtain ⟨t, finished⟩ := Table.correct (resetDiscarded v)
      (resetDiscarded_wellFormed v) (resetDiscarded_flow v) (resetDiscarded_chunkCodeFacts v)
      (resetDiscarded_callTargets v) blocks (Absorb.correct _) (resetDiscarded_tableCodeFacts v)
      (resetDiscarded_tableBlocks v _ stride
        (valid_return_boundary machine stack call.returnAddress).2.2)
      stride machine stack avoid call.returnAddress state loop count data separation within
    exact Or.inr ⟨loop.remaining, t, finished, output, frame⟩

end Sha2.Proofs.Reset
