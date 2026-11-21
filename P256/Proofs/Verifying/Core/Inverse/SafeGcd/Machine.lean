import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Core
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Functions

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l1170b0 => block_l1170b0 code hcode
  | .l1171a0 => block_l1171a0 code hcode
  | .l1141e0 => block_l1141e0 code hcode
  | .l114201 => block_l114201 code hcode
  | .l114285 => block_l114285 code hcode
  | .l1142ec => block_l1142ec code hcode
  | .l114300 => block_l114300 code hcode
  | .l114311 => block_l114311 code hcode
  | .l11435c => block_l11435c code hcode
  | .l1143a7 => block_l1143a7 code hcode
  | .l11441c => block_l11441c code hcode
  | .l11446c => block_l11446c code hcode
  | .l1144b3 => block_l1144b3 code hcode
  | .l11453e => block_l11453e code hcode
  | .l11454e => block_l11454e code hcode
  | .l114558 => block_l114558 code hcode
  | .l114560 => block_l114560 code hcode
  | .l114568 => block_l114568 code hcode
  | .l114574 => block_l114574 code hcode
  | .l1145af => block_l1145af code hcode
  | .l1145da => block_l1145da code hcode
  | .l1145e2 => block_l1145e2 code hcode
  | .l114616 => block_l114616 code hcode
  | .l114630 => block_l114630 code hcode
  | .l114635 => block_l114635 code hcode
  | .l11465b => block_l11465b code hcode
  | .l114675 => block_l114675 code hcode
  | .l11467a => block_l11467a code hcode
  | .l114680 => block_l114680 code hcode
  | .l11468d => block_l11468d code hcode
  | .l114698 => block_l114698 code hcode
  | .l1146d9 => block_l1146d9 code hcode
  | .l1181a0 => block_l1181a0 code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
