import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l116d00 => b_l116d00
  | .l1170b0 => b_l1170b0
  | .l1170c6 => b_l1170c6
  | .l1170d6 => b_l1170d6
  | .l1170db => b_l1170db
  | .l1170e3 => b_l1170e3
  | .l11715a => b_l11715a
  | .l117172 => b_l117172
  | .l11718a => b_l11718a

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
