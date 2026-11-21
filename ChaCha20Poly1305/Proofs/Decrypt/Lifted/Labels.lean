import ChaCha20Poly1305.Spec.Program.Extracted.Sections
import ChaCha20Poly1305.Proofs.Common.Lift.Simulation

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

inductive Label.G0 where
  | l1001f0
  | l10024c
  | l1002e5
  | l100384
  | l10038c
  | l1003ae
  | l1003e3
  | l100417
  | l100420
  | l10042c
  | l100435
  | l10043a
  | l10045a
  | l10046e
  | l100479
  | l10049a
  | l1004a0
  | l1004ac
  | l1004b5
  | l1004c2
  | l1004dd
  | l1004f1
  | l1004fc
  | l100520
  | l100577
  | l1005d2
  | l1005e4
  | l1005e8
  | l1005ea
  | l1005fc
  | l100620
  | l100a80
  | l100aae
  | l100ad0
  | l100b04
  | l100b10
  | l100b14
  | l100b30
  | l100b76
  | l100b7b
  | l100b90
  | l100ba5
  | l100bde
  | l100c70
  | l100cd0
  | l100d02
  | l100d26
  | l100d4a
  | l100d72
  | l100d94
  | l100dba
  | l100dea
  | l100e0e
  | l100e19
  | l100e8c
  | l100efe
  | l100f8e
  | l100fd0
  | l101036
  | l1010b3
  | l1010cc
  | l1010d5
  | l10111d
  | l101174

inductive Label.G1 where
  | l101180
  | l1011be
  | l1011e7
  | l10120f
  | l101233
  | l10125b
  | l101281
  | l1012b0
  | l1012d8
  | l1012e3
  | l10133c
  | l101386
  | l1013bf
  | l1013e3
  | l101420
  | l101467
  | l10146c
  | l101490
  | l1014a4
  | l1014a8
  | l1014aa
  | l1014c0
  | l101526
  | l10152c
  | l10153a
  | l101552
  | l101562
  | l101572
  | l10158b
  | l101596
  | l1015d4
  | l1015d8
  | l1015e5
  | l1015ed
  | l1015ff
  | l10160d
  | l101611
  | l101616
  | l101625
  | l101639
  | l10163b
  | l101aa0
  | l101ce0
  | l101d20
  | l101d69
  | l101db0
  | l101dec
  | l101e24
  | l101ab0
  | l101af1
  | l101b40
  | l101b85
  | l101bcd
  | l101c13
  | l101c63
  | l101ca5
  | l101e30
  | l101e40
  | l102020
  | l102026
  | l10202a
  | l102d70
  | l102dc0

inductive Label where
  | g0 (l : Label.G0)
  | g1 (l : Label.G1)

@[match_pattern] abbrev Label.l1001f0 : Label := .g0 .l1001f0
@[match_pattern] abbrev Label.l10024c : Label := .g0 .l10024c
@[match_pattern] abbrev Label.l1002e5 : Label := .g0 .l1002e5
@[match_pattern] abbrev Label.l100384 : Label := .g0 .l100384
@[match_pattern] abbrev Label.l10038c : Label := .g0 .l10038c
@[match_pattern] abbrev Label.l1003ae : Label := .g0 .l1003ae
@[match_pattern] abbrev Label.l1003e3 : Label := .g0 .l1003e3
@[match_pattern] abbrev Label.l100417 : Label := .g0 .l100417
@[match_pattern] abbrev Label.l100420 : Label := .g0 .l100420
@[match_pattern] abbrev Label.l10042c : Label := .g0 .l10042c
@[match_pattern] abbrev Label.l100435 : Label := .g0 .l100435
@[match_pattern] abbrev Label.l10043a : Label := .g0 .l10043a
@[match_pattern] abbrev Label.l10045a : Label := .g0 .l10045a
@[match_pattern] abbrev Label.l10046e : Label := .g0 .l10046e
@[match_pattern] abbrev Label.l100479 : Label := .g0 .l100479
@[match_pattern] abbrev Label.l10049a : Label := .g0 .l10049a
@[match_pattern] abbrev Label.l1004a0 : Label := .g0 .l1004a0
@[match_pattern] abbrev Label.l1004ac : Label := .g0 .l1004ac
@[match_pattern] abbrev Label.l1004b5 : Label := .g0 .l1004b5
@[match_pattern] abbrev Label.l1004c2 : Label := .g0 .l1004c2
@[match_pattern] abbrev Label.l1004dd : Label := .g0 .l1004dd
@[match_pattern] abbrev Label.l1004f1 : Label := .g0 .l1004f1
@[match_pattern] abbrev Label.l1004fc : Label := .g0 .l1004fc
@[match_pattern] abbrev Label.l100520 : Label := .g0 .l100520
@[match_pattern] abbrev Label.l100577 : Label := .g0 .l100577
@[match_pattern] abbrev Label.l1005d2 : Label := .g0 .l1005d2
@[match_pattern] abbrev Label.l1005e4 : Label := .g0 .l1005e4
@[match_pattern] abbrev Label.l1005e8 : Label := .g0 .l1005e8
@[match_pattern] abbrev Label.l1005ea : Label := .g0 .l1005ea
@[match_pattern] abbrev Label.l1005fc : Label := .g0 .l1005fc
@[match_pattern] abbrev Label.l100620 : Label := .g0 .l100620
@[match_pattern] abbrev Label.l100a80 : Label := .g0 .l100a80
@[match_pattern] abbrev Label.l100aae : Label := .g0 .l100aae
@[match_pattern] abbrev Label.l100ad0 : Label := .g0 .l100ad0
@[match_pattern] abbrev Label.l100b04 : Label := .g0 .l100b04
@[match_pattern] abbrev Label.l100b10 : Label := .g0 .l100b10
@[match_pattern] abbrev Label.l100b14 : Label := .g0 .l100b14
@[match_pattern] abbrev Label.l100b30 : Label := .g0 .l100b30
@[match_pattern] abbrev Label.l100b76 : Label := .g0 .l100b76
@[match_pattern] abbrev Label.l100b7b : Label := .g0 .l100b7b
@[match_pattern] abbrev Label.l100b90 : Label := .g0 .l100b90
@[match_pattern] abbrev Label.l100ba5 : Label := .g0 .l100ba5
@[match_pattern] abbrev Label.l100bde : Label := .g0 .l100bde
@[match_pattern] abbrev Label.l100c70 : Label := .g0 .l100c70
@[match_pattern] abbrev Label.l100cd0 : Label := .g0 .l100cd0
@[match_pattern] abbrev Label.l100d02 : Label := .g0 .l100d02
@[match_pattern] abbrev Label.l100d26 : Label := .g0 .l100d26
@[match_pattern] abbrev Label.l100d4a : Label := .g0 .l100d4a
@[match_pattern] abbrev Label.l100d72 : Label := .g0 .l100d72
@[match_pattern] abbrev Label.l100d94 : Label := .g0 .l100d94
@[match_pattern] abbrev Label.l100dba : Label := .g0 .l100dba
@[match_pattern] abbrev Label.l100dea : Label := .g0 .l100dea
@[match_pattern] abbrev Label.l100e0e : Label := .g0 .l100e0e
@[match_pattern] abbrev Label.l100e19 : Label := .g0 .l100e19
@[match_pattern] abbrev Label.l100e8c : Label := .g0 .l100e8c
@[match_pattern] abbrev Label.l100efe : Label := .g0 .l100efe
@[match_pattern] abbrev Label.l100f8e : Label := .g0 .l100f8e
@[match_pattern] abbrev Label.l100fd0 : Label := .g0 .l100fd0
@[match_pattern] abbrev Label.l101036 : Label := .g0 .l101036
@[match_pattern] abbrev Label.l1010b3 : Label := .g0 .l1010b3
@[match_pattern] abbrev Label.l1010cc : Label := .g0 .l1010cc
@[match_pattern] abbrev Label.l1010d5 : Label := .g0 .l1010d5
@[match_pattern] abbrev Label.l10111d : Label := .g0 .l10111d
@[match_pattern] abbrev Label.l101174 : Label := .g0 .l101174
@[match_pattern] abbrev Label.l101180 : Label := .g1 .l101180
@[match_pattern] abbrev Label.l1011be : Label := .g1 .l1011be
@[match_pattern] abbrev Label.l1011e7 : Label := .g1 .l1011e7
@[match_pattern] abbrev Label.l10120f : Label := .g1 .l10120f
@[match_pattern] abbrev Label.l101233 : Label := .g1 .l101233
@[match_pattern] abbrev Label.l10125b : Label := .g1 .l10125b
@[match_pattern] abbrev Label.l101281 : Label := .g1 .l101281
@[match_pattern] abbrev Label.l1012b0 : Label := .g1 .l1012b0
@[match_pattern] abbrev Label.l1012d8 : Label := .g1 .l1012d8
@[match_pattern] abbrev Label.l1012e3 : Label := .g1 .l1012e3
@[match_pattern] abbrev Label.l10133c : Label := .g1 .l10133c
@[match_pattern] abbrev Label.l101386 : Label := .g1 .l101386
@[match_pattern] abbrev Label.l1013bf : Label := .g1 .l1013bf
@[match_pattern] abbrev Label.l1013e3 : Label := .g1 .l1013e3
@[match_pattern] abbrev Label.l101420 : Label := .g1 .l101420
@[match_pattern] abbrev Label.l101467 : Label := .g1 .l101467
@[match_pattern] abbrev Label.l10146c : Label := .g1 .l10146c
@[match_pattern] abbrev Label.l101490 : Label := .g1 .l101490
@[match_pattern] abbrev Label.l1014a4 : Label := .g1 .l1014a4
@[match_pattern] abbrev Label.l1014a8 : Label := .g1 .l1014a8
@[match_pattern] abbrev Label.l1014aa : Label := .g1 .l1014aa
@[match_pattern] abbrev Label.l1014c0 : Label := .g1 .l1014c0
@[match_pattern] abbrev Label.l101526 : Label := .g1 .l101526
@[match_pattern] abbrev Label.l10152c : Label := .g1 .l10152c
@[match_pattern] abbrev Label.l10153a : Label := .g1 .l10153a
@[match_pattern] abbrev Label.l101552 : Label := .g1 .l101552
@[match_pattern] abbrev Label.l101562 : Label := .g1 .l101562
@[match_pattern] abbrev Label.l101572 : Label := .g1 .l101572
@[match_pattern] abbrev Label.l10158b : Label := .g1 .l10158b
@[match_pattern] abbrev Label.l101596 : Label := .g1 .l101596
@[match_pattern] abbrev Label.l1015d4 : Label := .g1 .l1015d4
@[match_pattern] abbrev Label.l1015d8 : Label := .g1 .l1015d8
@[match_pattern] abbrev Label.l1015e5 : Label := .g1 .l1015e5
@[match_pattern] abbrev Label.l1015ed : Label := .g1 .l1015ed
@[match_pattern] abbrev Label.l1015ff : Label := .g1 .l1015ff
@[match_pattern] abbrev Label.l10160d : Label := .g1 .l10160d
@[match_pattern] abbrev Label.l101611 : Label := .g1 .l101611
@[match_pattern] abbrev Label.l101616 : Label := .g1 .l101616
@[match_pattern] abbrev Label.l101625 : Label := .g1 .l101625
@[match_pattern] abbrev Label.l101639 : Label := .g1 .l101639
@[match_pattern] abbrev Label.l10163b : Label := .g1 .l10163b
@[match_pattern] abbrev Label.l101aa0 : Label := .g1 .l101aa0
@[match_pattern] abbrev Label.l101ce0 : Label := .g1 .l101ce0
@[match_pattern] abbrev Label.l101d20 : Label := .g1 .l101d20
@[match_pattern] abbrev Label.l101d69 : Label := .g1 .l101d69
@[match_pattern] abbrev Label.l101db0 : Label := .g1 .l101db0
@[match_pattern] abbrev Label.l101dec : Label := .g1 .l101dec
@[match_pattern] abbrev Label.l101e24 : Label := .g1 .l101e24
@[match_pattern] abbrev Label.l101ab0 : Label := .g1 .l101ab0
@[match_pattern] abbrev Label.l101af1 : Label := .g1 .l101af1
@[match_pattern] abbrev Label.l101b40 : Label := .g1 .l101b40
@[match_pattern] abbrev Label.l101b85 : Label := .g1 .l101b85
@[match_pattern] abbrev Label.l101bcd : Label := .g1 .l101bcd
@[match_pattern] abbrev Label.l101c13 : Label := .g1 .l101c13
@[match_pattern] abbrev Label.l101c63 : Label := .g1 .l101c63
@[match_pattern] abbrev Label.l101ca5 : Label := .g1 .l101ca5
@[match_pattern] abbrev Label.l101e30 : Label := .g1 .l101e30
@[match_pattern] abbrev Label.l101e40 : Label := .g1 .l101e40
@[match_pattern] abbrev Label.l102020 : Label := .g1 .l102020
@[match_pattern] abbrev Label.l102026 : Label := .g1 .l102026
@[match_pattern] abbrev Label.l10202a : Label := .g1 .l10202a
@[match_pattern] abbrev Label.l102d70 : Label := .g1 .l102d70
@[match_pattern] abbrev Label.l102dc0 : Label := .g1 .l102dc0

def Label.G0.address : Label.G0 → BitVec 64
  | .l1001f0 => 0x1001f0
  | .l10024c => 0x10024c
  | .l1002e5 => 0x1002e5
  | .l100384 => 0x100384
  | .l10038c => 0x10038c
  | .l1003ae => 0x1003ae
  | .l1003e3 => 0x1003e3
  | .l100417 => 0x100417
  | .l100420 => 0x100420
  | .l10042c => 0x10042c
  | .l100435 => 0x100435
  | .l10043a => 0x10043a
  | .l10045a => 0x10045a
  | .l10046e => 0x10046e
  | .l100479 => 0x100479
  | .l10049a => 0x10049a
  | .l1004a0 => 0x1004a0
  | .l1004ac => 0x1004ac
  | .l1004b5 => 0x1004b5
  | .l1004c2 => 0x1004c2
  | .l1004dd => 0x1004dd
  | .l1004f1 => 0x1004f1
  | .l1004fc => 0x1004fc
  | .l100520 => 0x100520
  | .l100577 => 0x100577
  | .l1005d2 => 0x1005d2
  | .l1005e4 => 0x1005e4
  | .l1005e8 => 0x1005e8
  | .l1005ea => 0x1005ea
  | .l1005fc => 0x1005fc
  | .l100620 => 0x100620
  | .l100a80 => 0x100a80
  | .l100aae => 0x100aae
  | .l100ad0 => 0x100ad0
  | .l100b04 => 0x100b04
  | .l100b10 => 0x100b10
  | .l100b14 => 0x100b14
  | .l100b30 => 0x100b30
  | .l100b76 => 0x100b76
  | .l100b7b => 0x100b7b
  | .l100b90 => 0x100b90
  | .l100ba5 => 0x100ba5
  | .l100bde => 0x100bde
  | .l100c70 => 0x100c70
  | .l100cd0 => 0x100cd0
  | .l100d02 => 0x100d02
  | .l100d26 => 0x100d26
  | .l100d4a => 0x100d4a
  | .l100d72 => 0x100d72
  | .l100d94 => 0x100d94
  | .l100dba => 0x100dba
  | .l100dea => 0x100dea
  | .l100e0e => 0x100e0e
  | .l100e19 => 0x100e19
  | .l100e8c => 0x100e8c
  | .l100efe => 0x100efe
  | .l100f8e => 0x100f8e
  | .l100fd0 => 0x100fd0
  | .l101036 => 0x101036
  | .l1010b3 => 0x1010b3
  | .l1010cc => 0x1010cc
  | .l1010d5 => 0x1010d5
  | .l10111d => 0x10111d
  | .l101174 => 0x101174

def Label.G0.live : Label.G0 → Nat
  | .l1001f0 => 0xc00800040f3fe
  | .l10024c => 0xc00800040f2fd
  | .l1002e5 => 0xc00800040f23d
  | .l100384 => 0xc008000406039
  | .l10038c => 0xc008000406038
  | .l1003ae => 0xc00800040f23d
  | .l1003e3 => 0xc00800040f27c
  | .l100417 => 0xc00800040f014
  | .l100420 => 0xc00800040f05c
  | .l10042c => 0xc00800040f23c
  | .l100435 => 0xc00800040f25c
  | .l10043a => 0xc00800040f258
  | .l10045a => 0xc00800040f230
  | .l10046e => 0xc00800040f03c
  | .l100479 => 0xc00800040925c
  | .l10049a => 0xc00800040f014
  | .l1004a0 => 0xc00800040f05c
  | .l1004ac => 0xc00800040f23c
  | .l1004b5 => 0xc00800040f25c
  | .l1004c2 => 0xc00800040f278
  | .l1004dd => 0xc00800040f230
  | .l1004f1 => 0xc00800040f03c
  | .l1004fc => 0xc00800040f03c
  | .l100520 => 0xc00800040f038
  | .l100577 => 0xc00800040f2bb
  | .l1005d2 => 0xc00800040f23c
  | .l1005e4 => 0xc0080004002d7
  | .l1005e8 => 0xc0080004002d7
  | .l1005ea => 0xc0080004002d7
  | .l1005fc => 0x0
  | .l100620 => 0x0
  | .l100a80 => 0xc00800040f2fc
  | .l100aae => 0xc008000401ed3
  | .l100ad0 => 0xc008000401ed6
  | .l100b04 => 0xc00800040de9e
  | .l100b10 => 0xc00800040de9f
  | .l100b14 => 0xc00800040dc9f
  | .l100b30 => 0xc00800040dedf
  | .l100b76 => 0xc00800040dedf
  | .l100b7b => 0xc00800040de9f
  | .l100b90 => 0xc00800040dedf
  | .l100ba5 => 0xc00800040dedf
  | .l100bde => 0xc008000405498
  | .l100c70 => 0xc008000401d90
  | .l100cd0 => 0xc00800040ffff
  | .l100d02 => 0xc00800040ffff
  | .l100d26 => 0xc00800040fffe
  | .l100d4a => 0xc00800040fffe
  | .l100d72 => 0xc00800040fffe
  | .l100d94 => 0xc00800040fffe
  | .l100dba => 0xc00800040fffe
  | .l100dea => 0xc00800040ffff
  | .l100e0e => 0xc00800040ffff
  | .l100e19 => 0xc00800040ffff
  | .l100e8c => 0xc00800040cfd3
  | .l100efe => 0xc008000401f91
  | .l100f8e => 0xc008000401f91
  | .l100fd0 => 0xc008000401f93
  | .l101036 => 0xc008000401f91
  | .l1010b3 => 0xc008000401257
  | .l1010cc => 0xc008000408ad7
  | .l1010d5 => 0xc008000400890
  | .l10111d => 0xc00800040ff7f
  | .l101174 => 0xc00800040fff7

def Label.G1.address : Label.G1 → BitVec 64
  | .l101180 => 0x101180
  | .l1011be => 0x1011be
  | .l1011e7 => 0x1011e7
  | .l10120f => 0x10120f
  | .l101233 => 0x101233
  | .l10125b => 0x10125b
  | .l101281 => 0x101281
  | .l1012b0 => 0x1012b0
  | .l1012d8 => 0x1012d8
  | .l1012e3 => 0x1012e3
  | .l10133c => 0x10133c
  | .l101386 => 0x101386
  | .l1013bf => 0x1013bf
  | .l1013e3 => 0x1013e3
  | .l101420 => 0x101420
  | .l101467 => 0x101467
  | .l10146c => 0x10146c
  | .l101490 => 0x101490
  | .l1014a4 => 0x1014a4
  | .l1014a8 => 0x1014a8
  | .l1014aa => 0x1014aa
  | .l1014c0 => 0x1014c0
  | .l101526 => 0x101526
  | .l10152c => 0x10152c
  | .l10153a => 0x10153a
  | .l101552 => 0x101552
  | .l101562 => 0x101562
  | .l101572 => 0x101572
  | .l10158b => 0x10158b
  | .l101596 => 0x101596
  | .l1015d4 => 0x1015d4
  | .l1015d8 => 0x1015d8
  | .l1015e5 => 0x1015e5
  | .l1015ed => 0x1015ed
  | .l1015ff => 0x1015ff
  | .l10160d => 0x10160d
  | .l101611 => 0x101611
  | .l101616 => 0x101616
  | .l101625 => 0x101625
  | .l101639 => 0x101639
  | .l10163b => 0x10163b
  | .l101aa0 => 0x101aa0
  | .l101ce0 => 0x101ce0
  | .l101d20 => 0x101d20
  | .l101d69 => 0x101d69
  | .l101db0 => 0x101db0
  | .l101dec => 0x101dec
  | .l101e24 => 0x101e24
  | .l101ab0 => 0x101ab0
  | .l101af1 => 0x101af1
  | .l101b40 => 0x101b40
  | .l101b85 => 0x101b85
  | .l101bcd => 0x101bcd
  | .l101c13 => 0x101c13
  | .l101c63 => 0x101c63
  | .l101ca5 => 0x101ca5
  | .l101e30 => 0x101e30
  | .l101e40 => 0x101e40
  | .l102020 => 0x102020
  | .l102026 => 0x102026
  | .l10202a => 0x10202a
  | .l102d70 => 0x102d70
  | .l102dc0 => 0x102dc0

def Label.G1.live : Label.G1 → Nat
  | .l101180 => 0xc00800040fff7
  | .l1011be => 0xc00800040ffff
  | .l1011e7 => 0xc00800040fbff
  | .l10120f => 0xc00800040fbff
  | .l101233 => 0xc00800040fbff
  | .l10125b => 0xc00800040fbf7
  | .l101281 => 0xc00800040fbf7
  | .l1012b0 => 0xc00800040fff7
  | .l1012d8 => 0xc00800040fff7
  | .l1012e3 => 0xc00800040fff7
  | .l10133c => 0xc00800040dff7
  | .l101386 => 0xc008000405fdf
  | .l1013bf => 0xc0080004042d5
  | .l1013e3 => 0xc008000404651
  | .l101420 => 0xc00800040cf5f
  | .l101467 => 0xc00800040cbdf
  | .l10146c => 0xc00800040cbdd
  | .l101490 => 0xc008000404a9f
  | .l1014a4 => 0xc0080004042d7
  | .l1014a8 => 0xc0080004002d7
  | .l1014aa => 0xc0080004002d7
  | .l1014c0 => 0xc00800040f3fe
  | .l101526 => 0xc0080004862f7
  | .l10152c => 0xc0080004062f7
  | .l10153a => 0xc00800040f218
  | .l101552 => 0xc00800040f239
  | .l101562 => 0xc00800040f239
  | .l101572 => 0xc00800040f238
  | .l10158b => 0xc00800040d2fe
  | .l101596 => 0xc00800040d038
  | .l1015d4 => 0xc00800040f2ff
  | .l1015d8 => 0xc00800040f23f
  | .l1015e5 => 0xc00800040f2fe
  | .l1015ed => 0xc00800040f238
  | .l1015ff => 0xc00800040f23c
  | .l10160d => 0xc0080004002d7
  | .l101611 => 0xc0080004002d6
  | .l101616 => 0xc0080004002d7
  | .l101625 => 0x0
  | .l101639 => 0x0
  | .l10163b => 0x0
  | .l101aa0 => 0xc00800040f2ff
  | .l101ce0 => 0xc00800040f0f8
  | .l101d20 => 0xc008000400957
  | .l101d69 => 0xc008000408fff
  | .l101db0 => 0xc0080004067df
  | .l101dec => 0xc0080004007d1
  | .l101e24 => 0xc0080004072df
  | .l101ab0 => 0xc00800040f0fc
  | .l101af1 => 0xc0080004005d7
  | .l101b40 => 0xc0080004097df
  | .l101b85 => 0xc00800040fdbe
  | .l101bcd => 0xc00800040dfff
  | .l101c13 => 0xc00800040fffe
  | .l101c63 => 0xc008000400d99
  | .l101ca5 => 0xc0080004006d7
  | .l101e30 => 0xc00800040f0fc
  | .l101e40 => 0xc00800040f0f8
  | .l102020 => 0xc00800040f2ff
  | .l102026 => 0xc00800040f2ff
  | .l10202a => 0xc00800040f2ff
  | .l102d70 => 0xc00800040f2fc
  | .l102dc0 => 0xc00800040f2fc

def address : Label → BitVec 64
  | .g0 l => l.address
  | .g1 l => l.address

def live : Label → Nat
  | .g0 l => l.live
  | .g1 l => l.live

def retLive : Nat := 0xc00800040f2ff

def textSection : Prelude.ImageSection :=
  ⟨ChaCha20Poly1305.Spec.Program.Extracted.textAddress, ChaCha20Poly1305.Spec.Program.Extracted.textBytes⟩

def rodataSection : Prelude.ImageSection :=
  ⟨ChaCha20Poly1305.Spec.Program.Extracted.rodataAddress, ChaCha20Poly1305.Spec.Program.Extracted.rodataBytes⟩

def sections : Prelude.ImageSections :=
  [textSection]

def fnCode : CodeMap := sections.toCodeMap

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
