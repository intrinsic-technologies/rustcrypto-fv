import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Functions
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Modular

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l116d00 => block_l116d00 code hcode
  | .l1171a0 => block_l1171a0 code hcode
  | .l1171be => block_l1171be code hcode
  | .l1171d2 => block_l1171d2 code hcode
  | .l117200 => block_l117200 code hcode
  | .l117244 => block_l117244 code hcode
  | .l117256 => block_l117256 code hcode
  | .l117287 => block_l117287 code hcode
  | .l1172b7 => block_l1172b7 code hcode
  | .l1172e7 => block_l1172e7 code hcode
  | .l11731a => block_l11731a code hcode
  | .l11734e => block_l11734e code hcode
  | .l117393 => block_l117393 code hcode
  | .l1173d1 => block_l1173d1 code hcode
  | .l1173e1 => block_l1173e1 code hcode
  | .l117405 => block_l117405 code hcode
  | .l117423 => block_l117423 code hcode
  | .l117457 => block_l117457 code hcode
  | .l117477 => block_l117477 code hcode
  | .l1174a0 => block_l1174a0 code hcode
  | .l1174d8 => block_l1174d8 code hcode
  | .l11750f => block_l11750f code hcode
  | .l11754e => block_l11754e code hcode
  | .l11758e => block_l11758e code hcode
  | .l1175c8 => block_l1175c8 code hcode
  | .l1175f2 => block_l1175f2 code hcode
  | .l117619 => block_l117619 code hcode
  | .l117631 => block_l117631 code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
