import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l116d00
  | l1171a0
  | l1171be
  | l1171d2
  | l117200
  | l117244
  | l117256
  | l117287
  | l1172b7
  | l1172e7
  | l11731a
  | l11734e
  | l117393
  | l1173d1
  | l1173e1
  | l117405
  | l117423
  | l117457
  | l117477
  | l1174a0
  | l1174d8
  | l11750f
  | l11754e
  | l11758e
  | l1175c8
  | l1175f2
  | l117619
  | l117631

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l116d00 : Label := .g0 .l116d00
@[match_pattern] abbrev Label.l1171a0 : Label := .g0 .l1171a0
@[match_pattern] abbrev Label.l1171be : Label := .g0 .l1171be
@[match_pattern] abbrev Label.l1171d2 : Label := .g0 .l1171d2
@[match_pattern] abbrev Label.l117200 : Label := .g0 .l117200
@[match_pattern] abbrev Label.l117244 : Label := .g0 .l117244
@[match_pattern] abbrev Label.l117256 : Label := .g0 .l117256
@[match_pattern] abbrev Label.l117287 : Label := .g0 .l117287
@[match_pattern] abbrev Label.l1172b7 : Label := .g0 .l1172b7
@[match_pattern] abbrev Label.l1172e7 : Label := .g0 .l1172e7
@[match_pattern] abbrev Label.l11731a : Label := .g0 .l11731a
@[match_pattern] abbrev Label.l11734e : Label := .g0 .l11734e
@[match_pattern] abbrev Label.l117393 : Label := .g0 .l117393
@[match_pattern] abbrev Label.l1173d1 : Label := .g0 .l1173d1
@[match_pattern] abbrev Label.l1173e1 : Label := .g0 .l1173e1
@[match_pattern] abbrev Label.l117405 : Label := .g0 .l117405
@[match_pattern] abbrev Label.l117423 : Label := .g0 .l117423
@[match_pattern] abbrev Label.l117457 : Label := .g0 .l117457
@[match_pattern] abbrev Label.l117477 : Label := .g0 .l117477
@[match_pattern] abbrev Label.l1174a0 : Label := .g0 .l1174a0
@[match_pattern] abbrev Label.l1174d8 : Label := .g0 .l1174d8
@[match_pattern] abbrev Label.l11750f : Label := .g0 .l11750f
@[match_pattern] abbrev Label.l11754e : Label := .g0 .l11754e
@[match_pattern] abbrev Label.l11758e : Label := .g0 .l11758e
@[match_pattern] abbrev Label.l1175c8 : Label := .g0 .l1175c8
@[match_pattern] abbrev Label.l1175f2 : Label := .g0 .l1175f2
@[match_pattern] abbrev Label.l117619 : Label := .g0 .l117619
@[match_pattern] abbrev Label.l117631 : Label := .g0 .l117631

def Label.G0.address : Label.G0 → BitVec 64
  | .l116d00 => 0x111220
  | .l1171a0 => 0x1116c0
  | .l1171be => 0x1116de
  | .l1171d2 => 0x1116f2
  | .l117200 => 0x111720
  | .l117244 => 0x111764
  | .l117256 => 0x111776
  | .l117287 => 0x1117a7
  | .l1172b7 => 0x1117d7
  | .l1172e7 => 0x111807
  | .l11731a => 0x11183a
  | .l11734e => 0x11186e
  | .l117393 => 0x1118b3
  | .l1173d1 => 0x1118f1
  | .l1173e1 => 0x111901
  | .l117405 => 0x111925
  | .l117423 => 0x111943
  | .l117457 => 0x111977
  | .l117477 => 0x111997
  | .l1174a0 => 0x1119c0
  | .l1174d8 => 0x1119f8
  | .l11750f => 0x111a2f
  | .l11754e => 0x111a6e
  | .l11758e => 0x111aae
  | .l1175c8 => 0x111ae8
  | .l1175f2 => 0x111b12
  | .l117619 => 0x111b39
  | .l117631 => 0x111b51

def Label.G0.live : Label.G0 → Nat
  | .l116d00 => 0x800800040ffff
  | .l1171a0 => 0x800800040ffff
  | .l1171be => 0x8008000400038
  | .l1171d2 => 0x800800040001a
  | .l117200 => 0x80080004003da
  | .l117244 => 0x800800040fd5f
  | .l117256 => 0x8008000407ddf
  | .l117287 => 0x8008000407dbf
  | .l1172b7 => 0x8008000407dbf
  | .l1172e7 => 0x8008000407cbf
  | .l11731a => 0x8008000407cb7
  | .l11734e => 0x8008000403c33
  | .l117393 => 0x8008000483d7b
  | .l1173d1 => 0x800800040ffff
  | .l1173e1 => 0x800800040ffff
  | .l117405 => 0x800800040c2df
  | .l117423 => 0x800800040e29e
  | .l117457 => 0x800800040feb5
  | .l117477 => 0x8008000403e3c
  | .l1174a0 => 0x8008000403e3d
  | .l1174d8 => 0x8008000403e7d
  | .l11750f => 0x8008000403efd
  | .l11754e => 0x8008000403bfd
  | .l11758e => 0x8008000401eff
  | .l1175c8 => 0x80080004019f3
  | .l1175f2 => 0x8008000400137
  | .l117619 => 0x8008000000000
  | .l117631 => 0x8008000000000

def address : Label → BitVec 64
  | .g0 l => l.address

def live : Label → Nat
  | .g0 l => l.live

def retLive : Nat := 0x800800040f03d

def textSection : Prelude.ImageSection :=
  ⟨P256.Spec.Program.Extracted.textAddress, P256.Spec.Program.Extracted.textBytes⟩

def sections : Prelude.ImageSections :=
  [textSection]

def fnCode : CodeMap := sections.toCodeMap

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
