import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l1170b0 => b_l1170b0
  | .l1171a0 => b_l1171a0
  | .l1141e0 => b_l1141e0
  | .l114201 => b_l114201
  | .l114285 => b_l114285
  | .l1142ec => b_l1142ec
  | .l114300 => b_l114300
  | .l114311 => b_l114311
  | .l11435c => b_l11435c
  | .l1143a7 => b_l1143a7
  | .l11441c => b_l11441c
  | .l11446c => b_l11446c
  | .l1144b3 => b_l1144b3
  | .l11453e => b_l11453e
  | .l11454e => b_l11454e
  | .l114558 => b_l114558
  | .l114560 => b_l114560
  | .l114568 => b_l114568
  | .l114574 => b_l114574
  | .l1145af => b_l1145af
  | .l1145da => b_l1145da
  | .l1145e2 => b_l1145e2
  | .l114616 => b_l114616
  | .l114630 => b_l114630
  | .l114635 => b_l114635
  | .l11465b => b_l11465b
  | .l114675 => b_l114675
  | .l11467a => b_l11467a
  | .l114680 => b_l114680
  | .l11468d => b_l11468d
  | .l114698 => b_l114698
  | .l1146d9 => b_l1146d9
  | .l1181a0 => b_l1181a0

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
