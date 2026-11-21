import P256.Proofs.SHA256.Compression.Values.Effects
import P256.Proofs.SHA256.Compression.Safety.Basic

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings]

structure StepRefinement (initial : RamState) (instruction : CheckedInstruction)
    (operation : Op) (position : Safety.Position) : Prop where
  valid : operation.StoreValid
  writes : ∀ model values, Safety.State initial model position →
    Represents (contextOfRam initial) values model →
    (instruction.effect model).writes = operation.writes (contextOfRam initial) values

theorem StepRefinement.next {initial : RamState} {instruction : CheckedInstruction}
    {operation : Op} {position : Safety.Position}
    (h : StepRefinement initial instruction operation position)
    (model : RamState) (values : Values) (state : Safety.State initial model position)
    (rep : Represents (contextOfRam initial) values model)
    (separate : RangeApart (stackPtr initial) 288 (initial.regValue .rsi) 64) :
    Represents (contextOfRam initial) (operation.eval (contextOfRam initial) values)
      (instruction.next model) := by
  have updated := operation.eval_represents_after (contextOfRam initial) values model rep h.valid separate
  rw [← h.writes model values state rep] at updated
  have obs := (instruction.effect model).after_obs model true
  have nextObs : Obs (applyWrites model (instruction.effect model).writes) (instruction.next model) :=
    ⟨obs.gpr.symm, fun x => (obs.mem x).symm, obs.zmm.symm, obs.rflags.symm, obs.mxcsr.symm,
      obs.fpr.symm, obs.fsw.symm, obs.ftw.symm, obs.fcw.symm, obs.fpuPtr.symm, obs.cs.symm⟩
  exact updated.of_obs nextObs

inductive TraceRefinement (initial : RamState) :
    List CheckedInstruction → List Op → Safety.Position → Safety.Position → List Safety.Position → Prop where
  | nil (position : Safety.Position) : TraceRefinement initial [] [] position position []
  | cons {instruction : CheckedInstruction} {rest : List CheckedInstruction}
      {operation : Op} {operations : List Op} {before middle after : Safety.Position}
      {positions : List Safety.Position}
      (step : StepRefinement initial instruction operation before)
      (tail : TraceRefinement initial rest operations middle after positions) :
      TraceRefinement initial (instruction :: rest) (operation :: operations) before after (middle :: positions)

namespace TraceRefinement

variable {initial : RamState} {instructions : List CheckedInstruction} {operations : List Op}
  {before after : Safety.Position} {positions : List Safety.Position}

theorem append {right : List CheckedInstruction} {moreOps : List Op}
    {finish : Safety.Position} {more : List Safety.Position}
    (left : TraceRefinement initial instructions operations before after positions)
    (rightCert : TraceRefinement initial right moreOps after finish more) :
    TraceRefinement initial (instructions ++ right) (operations ++ moreOps) before finish (positions ++ more) := by
  induction left with
  | nil => exact rightCert
  | cons step _ ih => exact .cons step (ih rightCert)

theorem result (cert : TraceRefinement initial instructions operations before after positions)
    (safe : Safety.Certificate initial instructions before after positions)
    (model : RamState) (values : Values) (state : Safety.State initial model before)
    (rep : Represents (contextOfRam initial) values model)
    (separate : RangeApart (stackPtr initial) 288 (initial.regValue .rsi) 64) :
    Represents (contextOfRam initial) (run (contextOfRam initial) operations values)
      (InstructionTrace.run instructions model) := by
  induction cert generalizing model values with
  | nil => exact rep
  | cons step tail ih =>
    cases safe with
    | cons safeStep safeTail =>
      exact ih safeTail ( _ ) ( _ ) (safeStep.next model state)
        (step.next model values state rep separate)

end TraceRefinement
end P256.Proofs.SHA256.Compression.Values
