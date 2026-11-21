import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Defs1
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Defs2
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Defs3
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Defs4
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Defs5

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def Label.G0.block : Label.G0 → Block Op Label signature Reg.count Reg.count
  | .l1001f0 => b_l1001f0
  | .l10024c => b_l10024c
  | .l1002e5 => b_l1002e5
  | .l100384 => b_l100384
  | .l10038c => b_l10038c
  | .l1003ae => b_l1003ae
  | .l1003e3 => b_l1003e3
  | .l100417 => b_l100417
  | .l100420 => b_l100420
  | .l10042c => b_l10042c
  | .l100435 => b_l100435
  | .l10043a => b_l10043a
  | .l10045a => b_l10045a
  | .l10046e => b_l10046e
  | .l100479 => b_l100479
  | .l10049a => b_l10049a
  | .l1004a0 => b_l1004a0
  | .l1004ac => b_l1004ac
  | .l1004b5 => b_l1004b5
  | .l1004c2 => b_l1004c2
  | .l1004dd => b_l1004dd
  | .l1004f1 => b_l1004f1
  | .l1004fc => b_l1004fc
  | .l100520 => b_l100520
  | .l100577 => b_l100577
  | .l1005d2 => b_l1005d2
  | .l1005e4 => b_l1005e4
  | .l1005e8 => b_l1005e8
  | .l1005ea => b_l1005ea
  | .l1005fc => b_l1005fc
  | .l100620 => b_l100620
  | .l100a80 => b_l100a80
  | .l100aae => b_l100aae
  | .l100ad0 => b_l100ad0
  | .l100b04 => b_l100b04
  | .l100b10 => b_l100b10
  | .l100b14 => b_l100b14
  | .l100b30 => b_l100b30
  | .l100b76 => b_l100b76
  | .l100b7b => b_l100b7b
  | .l100b90 => b_l100b90
  | .l100ba5 => b_l100ba5
  | .l100bde => b_l100bde
  | .l100c70 => b_l100c70
  | .l100cd0 => b_l100cd0
  | .l100d02 => b_l100d02
  | .l100d26 => b_l100d26
  | .l100d4a => b_l100d4a
  | .l100d72 => b_l100d72
  | .l100d94 => b_l100d94
  | .l100dba => b_l100dba
  | .l100dea => b_l100dea
  | .l100e0e => b_l100e0e
  | .l100e19 => b_l100e19
  | .l100e8c => b_l100e8c
  | .l100efe => b_l100efe
  | .l100f8e => b_l100f8e
  | .l100fd0 => b_l100fd0
  | .l101036 => b_l101036
  | .l1010b3 => b_l1010b3
  | .l1010cc => b_l1010cc
  | .l1010d5 => b_l1010d5
  | .l10111d => b_l10111d
  | .l101174 => b_l101174

@[cfg_block] def Label.G1.block : Label.G1 → Block Op Label signature Reg.count Reg.count
  | .l101180 => b_l101180
  | .l1011be => b_l1011be
  | .l1011e7 => b_l1011e7
  | .l10120f => b_l10120f
  | .l101233 => b_l101233
  | .l10125b => b_l10125b
  | .l101281 => b_l101281
  | .l1012b0 => b_l1012b0
  | .l1012d8 => b_l1012d8
  | .l1012e3 => b_l1012e3
  | .l10133c => b_l10133c
  | .l101386 => b_l101386
  | .l1013bf => b_l1013bf
  | .l1013e3 => b_l1013e3
  | .l101420 => b_l101420
  | .l101467 => b_l101467
  | .l10146c => b_l10146c
  | .l101490 => b_l101490
  | .l1014a4 => b_l1014a4
  | .l1014a8 => b_l1014a8
  | .l1014aa => b_l1014aa
  | .l1014c0 => b_l1014c0
  | .l101526 => b_l101526
  | .l10152c => b_l10152c
  | .l10153a => b_l10153a
  | .l101552 => b_l101552
  | .l101562 => b_l101562
  | .l101572 => b_l101572
  | .l10158b => b_l10158b
  | .l101596 => b_l101596
  | .l1015d4 => b_l1015d4
  | .l1015d8 => b_l1015d8
  | .l1015e5 => b_l1015e5
  | .l1015ed => b_l1015ed
  | .l1015ff => b_l1015ff
  | .l10160d => b_l10160d
  | .l101611 => b_l101611
  | .l101616 => b_l101616
  | .l101625 => b_l101625
  | .l101639 => b_l101639
  | .l10163b => b_l10163b
  | .l101aa0 => b_l101aa0
  | .l101ce0 => b_l101ce0
  | .l101d20 => b_l101d20
  | .l101d69 => b_l101d69
  | .l101db0 => b_l101db0
  | .l101dec => b_l101dec
  | .l101e24 => b_l101e24
  | .l101ab0 => b_l101ab0
  | .l101af1 => b_l101af1
  | .l101b40 => b_l101b40
  | .l101b85 => b_l101b85
  | .l101bcd => b_l101bcd
  | .l101c13 => b_l101c13
  | .l101c63 => b_l101c63
  | .l101ca5 => b_l101ca5
  | .l101e30 => b_l101e30
  | .l101e40 => b_l101e40
  | .l102020 => b_l102020
  | .l102026 => b_l102026
  | .l10202a => b_l10202a
  | .l102d70 => b_l102d70
  | .l102dc0 => b_l102dc0

def program : Program Op Label signature Reg.count where
  blocks
    | .g0 l => l.block
    | .g1 l => l.block

def lifted : Lifted := ⟨Label, address, live, retLive, program⟩

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
