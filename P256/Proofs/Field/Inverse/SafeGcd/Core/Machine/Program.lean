import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l1170b0 => b_l1170b0
  | .l1171a0 => b_l1171a0
  | .l117650 => b_l117650
  | .l117671 => b_l117671
  | .l1176da => b_l1176da
  | .l11774d => b_l11774d
  | .l117784 => b_l117784
  | .l1177a0 => b_l1177a0
  | .l1177b1 => b_l1177b1
  | .l1177fc => b_l1177fc
  | .l117849 => b_l117849
  | .l1178bb => b_l1178bb
  | .l11790e => b_l11790e
  | .l11795a => b_l11795a
  | .l1179df => b_l1179df
  | .l1179fa => b_l1179fa
  | .l117a59 => b_l117a59
  | .l117aa0 => b_l117aa0
  | .l117b01 => b_l117b01
  | .l117b46 => b_l117b46
  | .l117b83 => b_l117b83
  | .l117bc2 => b_l117bc2
  | .l117bdb => b_l117bdb
  | .l117be3 => b_l117be3
  | .l117be8 => b_l117be8
  | .l117c2f => b_l117c2f
  | .l1181a0 => b_l1181a0

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
