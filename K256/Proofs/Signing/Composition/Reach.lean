import K256.Proofs.Signing.Composition.State
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Composition

open CFG Lift

theorem appendStack {x y : LIR.lifted.State} (path : Reach x y)
    (rest : List LIR.lifted.StackFrame) :
    Reach ⟨x.location,x.stack ++ rest⟩ ⟨y.location,y.stack ++ rest⟩ := by
  induction path with
  | refl => exact .refl _
  | step first _ ih => exact .step (ParseSignature.step_append_stack first rest) ih

end K256.Proofs.Signing.Composition
