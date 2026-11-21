import P256.Proofs.Sec1.SquareRoot.Square.Wide.StoreHighStage

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 1000000 in
theorem storeHighStageEffect_eq (s : RamState) : storeHighStageEffect s = bodyEffect s := by
  simp only [storeHighStageEffect, bodyEffect, sourceWords, squareWords, crossWords]
  rfl

theorem body_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BodyPre (codeRange 0x11cbb8 bodyBytes)
      (Effect.post bodyEffect) := by
  simpa only [funext storeHighStageEffect_eq] using storeHighStage_correct boundary hout

end P256.Proofs.Sec1.SquareRoot.Square.Wide
