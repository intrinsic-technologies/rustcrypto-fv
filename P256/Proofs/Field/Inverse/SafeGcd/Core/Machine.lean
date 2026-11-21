import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Core
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Functions

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem Label.G0.liftedBlock [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l1170b0 => block_l1170b0 code hcode
  | .l1171a0 => block_l1171a0 code hcode
  | .l117650 => block_l117650 code hcode
  | .l117671 => block_l117671 code hcode
  | .l1176da => block_l1176da code hcode
  | .l11774d => block_l11774d code hcode
  | .l117784 => block_l117784 code hcode
  | .l1177a0 => block_l1177a0 code hcode
  | .l1177b1 => block_l1177b1 code hcode
  | .l1177fc => block_l1177fc code hcode
  | .l117849 => block_l117849 code hcode
  | .l1178bb => block_l1178bb code hcode
  | .l11790e => block_l11790e code hcode
  | .l11795a => block_l11795a code hcode
  | .l1179df => block_l1179df code hcode
  | .l1179fa => block_l1179fa code hcode
  | .l117a59 => block_l117a59 code hcode
  | .l117aa0 => block_l117aa0 code hcode
  | .l117b01 => block_l117b01 code hcode
  | .l117b46 => block_l117b46 code hcode
  | .l117b83 => block_l117b83 code hcode
  | .l117bc2 => block_l117bc2 code hcode
  | .l117bdb => block_l117bdb code hcode
  | .l117be3 => block_l117be3 code hcode
  | .l117be8 => block_l117be8 code hcode
  | .l117c2f => block_l117c2f code hcode
  | .l1181a0 => block_l1181a0 code hcode

theorem blocks [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock code hcode l

theorem simulation [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  Lifted.simulation (P := lifted) (blocks code hcode) hout

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
