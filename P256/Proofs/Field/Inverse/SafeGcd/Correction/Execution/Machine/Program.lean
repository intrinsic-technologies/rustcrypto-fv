import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l1181a0 => b_l1181a0
  | .l1181ad => b_l1181ad
  | .l1181e3 => b_l1181e3
  | .l11821e => b_l11821e
  | .l118251 => b_l118251
  | .l118288 => b_l118288
  | .l1182a7 => b_l1182a7
  | .l1182f8 => b_l1182f8

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
