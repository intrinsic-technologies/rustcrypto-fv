import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l1170b0
  | l1171a0
  | l117650
  | l117671
  | l1176da
  | l11774d
  | l117784
  | l1177a0
  | l1177b1
  | l1177fc
  | l117849
  | l1178bb
  | l11790e
  | l11795a
  | l1179df
  | l1179fa
  | l117a59
  | l117aa0
  | l117b01
  | l117b46
  | l117b83
  | l117bc2
  | l117bdb
  | l117be3
  | l117be8
  | l117c2f
  | l1181a0

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l1170b0 : Label := .g0 .l1170b0
@[match_pattern] abbrev Label.l1171a0 : Label := .g0 .l1171a0
@[match_pattern] abbrev Label.l117650 : Label := .g0 .l117650
@[match_pattern] abbrev Label.l117671 : Label := .g0 .l117671
@[match_pattern] abbrev Label.l1176da : Label := .g0 .l1176da
@[match_pattern] abbrev Label.l11774d : Label := .g0 .l11774d
@[match_pattern] abbrev Label.l117784 : Label := .g0 .l117784
@[match_pattern] abbrev Label.l1177a0 : Label := .g0 .l1177a0
@[match_pattern] abbrev Label.l1177b1 : Label := .g0 .l1177b1
@[match_pattern] abbrev Label.l1177fc : Label := .g0 .l1177fc
@[match_pattern] abbrev Label.l117849 : Label := .g0 .l117849
@[match_pattern] abbrev Label.l1178bb : Label := .g0 .l1178bb
@[match_pattern] abbrev Label.l11790e : Label := .g0 .l11790e
@[match_pattern] abbrev Label.l11795a : Label := .g0 .l11795a
@[match_pattern] abbrev Label.l1179df : Label := .g0 .l1179df
@[match_pattern] abbrev Label.l1179fa : Label := .g0 .l1179fa
@[match_pattern] abbrev Label.l117a59 : Label := .g0 .l117a59
@[match_pattern] abbrev Label.l117aa0 : Label := .g0 .l117aa0
@[match_pattern] abbrev Label.l117b01 : Label := .g0 .l117b01
@[match_pattern] abbrev Label.l117b46 : Label := .g0 .l117b46
@[match_pattern] abbrev Label.l117b83 : Label := .g0 .l117b83
@[match_pattern] abbrev Label.l117bc2 : Label := .g0 .l117bc2
@[match_pattern] abbrev Label.l117bdb : Label := .g0 .l117bdb
@[match_pattern] abbrev Label.l117be3 : Label := .g0 .l117be3
@[match_pattern] abbrev Label.l117be8 : Label := .g0 .l117be8
@[match_pattern] abbrev Label.l117c2f : Label := .g0 .l117c2f
@[match_pattern] abbrev Label.l1181a0 : Label := .g0 .l1181a0

def Label.G0.address : Label.G0 → BitVec 64
  | .l1170b0 => 0x1115d0
  | .l1171a0 => 0x1116c0
  | .l117650 => 0x111b70
  | .l117671 => 0x111b91
  | .l1176da => 0x111bfa
  | .l11774d => 0x111c6d
  | .l117784 => 0x111ca4
  | .l1177a0 => 0x111cc0
  | .l1177b1 => 0x111cd1
  | .l1177fc => 0x111d1c
  | .l117849 => 0x111d69
  | .l1178bb => 0x111ddb
  | .l11790e => 0x111e2e
  | .l11795a => 0x111e7a
  | .l1179df => 0x111eff
  | .l1179fa => 0x111f1a
  | .l117a59 => 0x111f79
  | .l117aa0 => 0x111fc0
  | .l117b01 => 0x112021
  | .l117b46 => 0x112066
  | .l117b83 => 0x1120a3
  | .l117bc2 => 0x1120e2
  | .l117bdb => 0x1120fb
  | .l117be3 => 0x112103
  | .l117be8 => 0x112108
  | .l117c2f => 0x11214f
  | .l1181a0 => 0x1126c0

def Label.G0.live : Label.G0 → Nat
  | .l1170b0 => 0x800800040ffff
  | .l1171a0 => 0x800800040ffff
  | .l117650 => 0x800800040ffff
  | .l117671 => 0x8008000404d5c
  | .l1176da => 0x8008000404f58
  | .l11774d => 0x8008000404f18
  | .l117784 => 0x8008000404e18
  | .l1177a0 => 0x8008000406c38
  | .l1177b1 => 0x800800040fc38
  | .l1177fc => 0x800800040fc38
  | .l117849 => 0x800800040fc38
  | .l1178bb => 0x800800040fc38
  | .l11790e => 0x800800040fc38
  | .l11795a => 0x800800040fd38
  | .l1179df => 0x800800040fd38
  | .l1179fa => 0x8008000406e3c
  | .l117a59 => 0x8008000406376
  | .l117aa0 => 0x80080004070f7
  | .l117b01 => 0x8008000407ffb
  | .l117b46 => 0x8008000407ff7
  | .l117b83 => 0x800800040ffff
  | .l117bc2 => 0x800800040fdbf
  | .l117bdb => 0x800800040fcff
  | .l117be3 => 0x800800040fc38
  | .l117be8 => 0x800800040bf38
  | .l117c2f => 0x8008000404d1c
  | .l1181a0 => 0x800800040ffff

def address : Label → BitVec 64
  | .g0 l => l.address

def live : Label → Nat
  | .g0 l => l.live

def retLive : Nat := 0x800800040fd3d

def textSection : Prelude.ImageSection :=
  ⟨P256.Spec.Program.Extracted.textAddress, P256.Spec.Program.Extracted.textBytes⟩

def sections : Prelude.ImageSections :=
  [textSection]

def fnCode : CodeMap := sections.toCodeMap

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
