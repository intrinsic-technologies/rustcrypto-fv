import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Iteration

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

theorem correct [Bindings] (l : Layout) : Contract l := by
  intro initial s n reserve regions inputs wf flow chunkCode targets chunkBlocks
    chunkCorrect code blocks stride machine stack avoids returnAddress state loop
    count data separation within
  let ctx : Context l initial regions reserve :=
    ⟨wf, flow, chunkCode, targets, chunkBlocks, chunkCorrect, code, blocks, stride,
      machine, stack, avoids, returnAddress, within⟩
  have copyIndex : ∀ call ∈ [l.chunk.smallCall, l.chunk.fillCall, l.chunk.tailCall], ∀ r,
      call.encoding = .register r → r ≠ l.index := by
    intro call member r encoding same
    have copied := loop.copyRegister call member r encoding
    rw [same, loop.indexRegister] at copied
    exact (by decide : (0 : BitVec 64) ≠ 0x10dd60) copied
  have loop_run : ∀ remaining index current, index + remaining = inputs.size →
      ExecutionState initial current regions → LoopState l (l.chunk.sp initial) inputs index current →
      InputData l (l.chunk.sp initial) inputs current →
      Separation l initial current reserve inputs → CountAt l (l.chunk.sp initial) current →
      ∃ t, Finished l initial current t regions inputs := by
    intro remaining
    induction remaining with
    | zero =>
      intro index current total state loop data separation count
      have pending := loop.remaining
      omega
    | succ remaining ih =>
      intro index current total state loop data separation count
      obtain ⟨advanced, stateNext, dataNext, separationNext, countNext, memoryNext,
        registersNext, step⟩ := iteration ctx state loop data separation count copyIndex
      rcases step with continuing | ⟨rip, rsp, hash, finalCount⟩
      · obtain ⟨t, finished⟩ := ih (index + 1) advanced (by omega)
          stateNext continuing dataNext separationNext countNext
        refine ⟨t, finished.state, finished.rip, finished.rsp, finished.hasher, finished.count,
          memoryWriteFrame_trans memoryNext finished.memory, ?_⟩
        intro r small kept
        exact (finished.registers r small kept).trans (registersNext r small kept)
      · exact ⟨advanced, stateNext, rip, rsp, hash, finalCount, memoryNext, registersNext⟩
  exact loop_run inputs.size 0 s (by omega) state loop data separation count

end Sha2.Proofs.Common.SHA256.Absorb.Table
