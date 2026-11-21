import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Inverse.Wrapper.Machine.Defs

namespace P256.Proofs.Scalar.Inverse.Wrapper.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l118910 => b_l118910
  | .l11893a => b_l11893a
  | .l118966 => b_l118966
  | .l117650 => b_l117650
  | .l126f60 => b_l126f60

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Scalar.Inverse.Wrapper.Machine
