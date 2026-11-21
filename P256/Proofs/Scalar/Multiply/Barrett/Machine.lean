import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Eval
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Reduce

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l118320 => block_l118320 code hcode
  | .l11832e => block_l11832e code hcode
  | .l11839b => block_l11839b code hcode
  | .l118420 => block_l118420 code hcode
  | .l1184ac => block_l1184ac code hcode
  | .l118544 => block_l118544 code hcode
  | .l1185d2 => block_l1185d2 code hcode
  | .l118654 => block_l118654 code hcode
  | .l1186f3 => block_l1186f3 code hcode
  | .l118722 => block_l118722 code hcode
  | .l118752 => block_l118752 code hcode
  | .l118782 => block_l118782 code hcode
  | .l1187b8 => block_l1187b8 code hcode
  | .l1187ed => block_l1187ed code hcode
  | .l11880b => block_l11880b code hcode
  | .l118837 => block_l118837 code hcode
  | .l118856 => block_l118856 code hcode
  | .l118882 => block_l118882 code hcode
  | .l1188a1 => block_l1188a1 code hcode
  | .l1188c5 => block_l1188c5 code hcode
  | .l1188e7 => block_l1188e7 code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (P256.Proofs.Lift.dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Scalar.Multiply.Barrett.Machine
