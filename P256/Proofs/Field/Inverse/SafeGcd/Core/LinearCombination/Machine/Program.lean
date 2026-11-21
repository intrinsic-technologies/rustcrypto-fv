import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l116d00 => b_l116d00
  | .l116d0e => b_l116d0e
  | .l116d4e => b_l116d4e
  | .l116d95 => b_l116d95
  | .l116de3 => b_l116de3
  | .l116e0f => b_l116e0f
  | .l116e59 => b_l116e59
  | .l116e9d => b_l116e9d
  | .l116eb9 => b_l116eb9
  | .l116ede => b_l116ede
  | .l116f0b => b_l116f0b
  | .l116f39 => b_l116f39
  | .l116f67 => b_l116f67
  | .l116fbb => b_l116fbb
  | .l116fd8 => b_l116fd8
  | .l11700a => b_l11700a
  | .l117033 => b_l117033
  | .l117072 => b_l117072
  | .l117080 => b_l117080

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
