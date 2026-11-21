import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Defs

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l118320 => b_l118320
  | .l11832e => b_l11832e
  | .l11839b => b_l11839b
  | .l118420 => b_l118420
  | .l1184ac => b_l1184ac
  | .l118544 => b_l118544
  | .l1185d2 => b_l1185d2
  | .l118654 => b_l118654
  | .l1186f3 => b_l1186f3
  | .l118722 => b_l118722
  | .l118752 => b_l118752
  | .l118782 => b_l118782
  | .l1187b8 => b_l1187b8
  | .l1187ed => b_l1187ed
  | .l11880b => b_l11880b
  | .l118837 => b_l118837
  | .l118856 => b_l118856
  | .l118882 => b_l118882
  | .l1188a1 => b_l1188a1
  | .l1188c5 => b_l1188c5
  | .l1188e7 => b_l1188e7

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Scalar.Multiply.Barrett.Machine
