import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Functions

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l116d00 => block_l116d00 code hcode
  | .l1170b0 => block_l1170b0 code hcode
  | .l1170c6 => block_l1170c6 code hcode
  | .l1170d6 => block_l1170d6 code hcode
  | .l1170db => block_l1170db code hcode
  | .l1170e3 => block_l1170e3 code hcode
  | .l11715a => block_l11715a code hcode
  | .l117172 => block_l117172 code hcode
  | .l11718a => block_l11718a code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
