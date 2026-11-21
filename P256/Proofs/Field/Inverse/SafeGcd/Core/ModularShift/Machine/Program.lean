import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l116d00 => b_l116d00
  | .l1171a0 => b_l1171a0
  | .l1171be => b_l1171be
  | .l1171d2 => b_l1171d2
  | .l117200 => b_l117200
  | .l117244 => b_l117244
  | .l117256 => b_l117256
  | .l117287 => b_l117287
  | .l1172b7 => b_l1172b7
  | .l1172e7 => b_l1172e7
  | .l11731a => b_l11731a
  | .l11734e => b_l11734e
  | .l117393 => b_l117393
  | .l1173d1 => b_l1173d1
  | .l1173e1 => b_l1173e1
  | .l117405 => b_l117405
  | .l117423 => b_l117423
  | .l117457 => b_l117457
  | .l117477 => b_l117477
  | .l1174a0 => b_l1174a0
  | .l1174d8 => b_l1174d8
  | .l11750f => b_l11750f
  | .l11754e => b_l11754e
  | .l11758e => b_l11758e
  | .l1175c8 => b_l1175c8
  | .l1175f2 => b_l1175f2
  | .l117619 => b_l117619
  | .l117631 => b_l117631

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
