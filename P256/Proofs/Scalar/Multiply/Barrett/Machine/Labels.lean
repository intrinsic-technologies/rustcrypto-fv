import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l118320
  | l11832e
  | l11839b
  | l118420
  | l1184ac
  | l118544
  | l1185d2
  | l118654
  | l1186f3
  | l118722
  | l118752
  | l118782
  | l1187b8
  | l1187ed
  | l11880b
  | l118837
  | l118856
  | l118882
  | l1188a1
  | l1188c5
  | l1188e7

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l118320 : Label := .g0 .l118320
@[match_pattern] abbrev Label.l11832e : Label := .g0 .l11832e
@[match_pattern] abbrev Label.l11839b : Label := .g0 .l11839b
@[match_pattern] abbrev Label.l118420 : Label := .g0 .l118420
@[match_pattern] abbrev Label.l1184ac : Label := .g0 .l1184ac
@[match_pattern] abbrev Label.l118544 : Label := .g0 .l118544
@[match_pattern] abbrev Label.l1185d2 : Label := .g0 .l1185d2
@[match_pattern] abbrev Label.l118654 : Label := .g0 .l118654
@[match_pattern] abbrev Label.l1186f3 : Label := .g0 .l1186f3
@[match_pattern] abbrev Label.l118722 : Label := .g0 .l118722
@[match_pattern] abbrev Label.l118752 : Label := .g0 .l118752
@[match_pattern] abbrev Label.l118782 : Label := .g0 .l118782
@[match_pattern] abbrev Label.l1187b8 : Label := .g0 .l1187b8
@[match_pattern] abbrev Label.l1187ed : Label := .g0 .l1187ed
@[match_pattern] abbrev Label.l11880b : Label := .g0 .l11880b
@[match_pattern] abbrev Label.l118837 : Label := .g0 .l118837
@[match_pattern] abbrev Label.l118856 : Label := .g0 .l118856
@[match_pattern] abbrev Label.l118882 : Label := .g0 .l118882
@[match_pattern] abbrev Label.l1188a1 : Label := .g0 .l1188a1
@[match_pattern] abbrev Label.l1188c5 : Label := .g0 .l1188c5
@[match_pattern] abbrev Label.l1188e7 : Label := .g0 .l1188e7

def Label.G0.address : Label.G0 → BitVec 64
  | .l118320 => 0x112840
  | .l11832e => 0x11284e
  | .l11839b => 0x1128bb
  | .l118420 => 0x112940
  | .l1184ac => 0x1129cc
  | .l118544 => 0x112a64
  | .l1185d2 => 0x112af2
  | .l118654 => 0x112b74
  | .l1186f3 => 0x112c13
  | .l118722 => 0x112c42
  | .l118752 => 0x112c72
  | .l118782 => 0x112ca2
  | .l1187b8 => 0x112cd8
  | .l1187ed => 0x112d0d
  | .l11880b => 0x112d2b
  | .l118837 => 0x112d57
  | .l118856 => 0x112d76
  | .l118882 => 0x112da2
  | .l1188a1 => 0x112dc1
  | .l1188c5 => 0x112de5
  | .l1188e7 => 0x112e07

def Label.G0.live : Label.G0 → Nat
  | .l118320 => 0x800800040f0fc
  | .l11832e => 0x80080004000d4
  | .l11839b => 0x8008000413ef8
  | .l118420 => 0x800800040f798
  | .l1184ac => 0x800800040fc93
  | .l118544 => 0x8008000408fbb
  | .l1185d2 => 0x800800041c0de
  | .l118654 => 0x800800040df9b
  | .l1186f3 => 0x800800040e39f
  | .l118722 => 0x800800040e3db
  | .l118752 => 0x800800040e2df
  | .l118782 => 0x800800040c2df
  | .l1187b8 => 0x80080004083dd
  | .l1187ed => 0x80080004086d7
  | .l11880b => 0x80080004087d7
  | .l118837 => 0x80080004087d7
  | .l118856 => 0x80080004087d7
  | .l118882 => 0x80080004083d7
  | .l1188a1 => 0x80080004081d7
  | .l1188c5 => 0x8008000408bd7
  | .l1188e7 => 0x8008000408b95

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

end P256.Proofs.Scalar.Multiply.Barrett.Machine
