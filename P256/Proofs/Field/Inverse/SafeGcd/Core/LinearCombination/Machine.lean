import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.LinearCombination

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l116d00 => block_l116d00 code hcode
  | .l116d0e => block_l116d0e code hcode
  | .l116d4e => block_l116d4e code hcode
  | .l116d95 => block_l116d95 code hcode
  | .l116de3 => block_l116de3 code hcode
  | .l116e0f => block_l116e0f code hcode
  | .l116e59 => block_l116e59 code hcode
  | .l116e9d => block_l116e9d code hcode
  | .l116eb9 => block_l116eb9 code hcode
  | .l116ede => block_l116ede code hcode
  | .l116f0b => block_l116f0b code hcode
  | .l116f39 => block_l116f39 code hcode
  | .l116f67 => block_l116f67 code hcode
  | .l116fbb => block_l116fbb code hcode
  | .l116fd8 => block_l116fd8 code hcode
  | .l11700a => block_l11700a code hcode
  | .l117033 => block_l117033 code hcode
  | .l117072 => block_l117072 code hcode
  | .l117080 => block_l117080 code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
