import P256.Proofs.Field.Montgomery.Reduction.Return.Epilogue
import P256.Proofs.Field.Montgomery.Reduction.Return.Frame

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_body [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : BinaryFieldPre s boundary 0x113c10 56) (entry : Entry s t boundary)
    (execution : ∃ fuel, Advances boundary fuel t u)
    (ready : ReadyToStep u) (rip : u.RIP = 0x113dea)
    (frame : AgreesExcept (scratchComponents t) t u) :
    ∃ final, CalleeResult s final boundary 32 56 ∧
      Nat256At final (s.regValue .rdi) (outputLimbs u).toNat := by
  obtain ⟨v, ⟨storeFuel, storeRun⟩, storeReady, storeRip, stores, output⟩ :=
    store_body pre entry ready rip frame
  have work := Return.work_frame pre entry frame stores
  have wholeFrame := Return.whole_frame pre entry work
  have wholeAgrees := (entry.agrees.trans frame).trans stores
  obtain ⟨saved, returnSlot⟩ := Return.saved_slots pre entry work
  have stage : Return.EpiloguePre s v
      (prologueComponents s ++ scratchComponents t ++ [.mem (s.regValue .rdi) 32, .rip]) := by
    refine ⟨storeReady, ScalarFrame.loaded_of_frame pre.toCalleePre wholeFrame,
      storeRip, ?_, saved, returnSlot, wholeAgrees⟩
    exact (stores.read (n := 64) (r := 4) (by simp)).trans
      ((frame.read (n := 64) (r := 4)
        (by simp [scratchComponents, registerClobbers])).trans entry.rsp)
  obtain ⟨final, result⟩ := Return.epilogue_correct pre.toCalleePre stage
    (by simp [prologueComponents, saveFrame, scratchComponents, registerClobbers])
    (by simp [prologueComponents, saveFrame, scratchComponents, registerClobbers])
    (by simp [prologueComponents, saveFrame, scratchComponents, registerClobbers])
  obtain ⟨bodyFuel, bodyRun⟩ := execution
  refine ⟨final, ?_, ?_⟩
  · refine ⟨⟨7 + bodyFuel + storeFuel + 8,
      ((entry.execution.trans bodyRun).trans storeRun).trans result.execution⟩,
      result.rip, result.rsp, result.bindingsSupported, result.machine,
      result.calleeSaved, result.directionFlag, result.mxcsr, result.fp87,
      ?_, result.loaded, (wholeAgrees.trans result.agrees).grow⟩
    intro a ha
    rw [result.external]
    exact wholeFrame a ha
  · exact ⟨output.1, fun i hi => by rw [result.external]; exact output.2 i hi⟩

end P256.Proofs.Field.Montgomery.Reduction
