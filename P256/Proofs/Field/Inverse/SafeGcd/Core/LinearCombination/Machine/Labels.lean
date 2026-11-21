import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l116d00
  | l116d0e
  | l116d4e
  | l116d95
  | l116de3
  | l116e0f
  | l116e59
  | l116e9d
  | l116eb9
  | l116ede
  | l116f0b
  | l116f39
  | l116f67
  | l116fbb
  | l116fd8
  | l11700a
  | l117033
  | l117072
  | l117080

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l116d00 : Label := .g0 .l116d00
@[match_pattern] abbrev Label.l116d0e : Label := .g0 .l116d0e
@[match_pattern] abbrev Label.l116d4e : Label := .g0 .l116d4e
@[match_pattern] abbrev Label.l116d95 : Label := .g0 .l116d95
@[match_pattern] abbrev Label.l116de3 : Label := .g0 .l116de3
@[match_pattern] abbrev Label.l116e0f : Label := .g0 .l116e0f
@[match_pattern] abbrev Label.l116e59 : Label := .g0 .l116e59
@[match_pattern] abbrev Label.l116e9d : Label := .g0 .l116e9d
@[match_pattern] abbrev Label.l116eb9 : Label := .g0 .l116eb9
@[match_pattern] abbrev Label.l116ede : Label := .g0 .l116ede
@[match_pattern] abbrev Label.l116f0b : Label := .g0 .l116f0b
@[match_pattern] abbrev Label.l116f39 : Label := .g0 .l116f39
@[match_pattern] abbrev Label.l116f67 : Label := .g0 .l116f67
@[match_pattern] abbrev Label.l116fbb : Label := .g0 .l116fbb
@[match_pattern] abbrev Label.l116fd8 : Label := .g0 .l116fd8
@[match_pattern] abbrev Label.l11700a : Label := .g0 .l11700a
@[match_pattern] abbrev Label.l117033 : Label := .g0 .l117033
@[match_pattern] abbrev Label.l117072 : Label := .g0 .l117072
@[match_pattern] abbrev Label.l117080 : Label := .g0 .l117080

def Label.G0.address : Label.G0 → BitVec 64
  | .l116d00 => 0x111220
  | .l116d0e => 0x11122e
  | .l116d4e => 0x11126e
  | .l116d95 => 0x1112b5
  | .l116de3 => 0x111303
  | .l116e0f => 0x11132f
  | .l116e59 => 0x111379
  | .l116e9d => 0x1113bd
  | .l116eb9 => 0x1113d9
  | .l116ede => 0x1113fe
  | .l116f0b => 0x11142b
  | .l116f39 => 0x111459
  | .l116f67 => 0x111487
  | .l116fbb => 0x1114db
  | .l116fd8 => 0x1114f8
  | .l11700a => 0x11152a
  | .l117033 => 0x111553
  | .l117072 => 0x111592
  | .l117080 => 0x1115a0

def Label.G0.live : Label.G0 → Nat
  | .l116d00 => 0x800800040f1fe
  | .l116d0e => 0x80080004001d6
  | .l116d4e => 0x80080004009d9
  | .l116d95 => 0x800800040fefa
  | .l116de3 => 0x800800040dfbf
  | .l116e0f => 0x80080004097df
  | .l116e59 => 0x800800040ffbf
  | .l116e9d => 0x8008000403fff
  | .l116eb9 => 0x800800040b7fa
  | .l116ede => 0x800800040f7bb
  | .l116f0b => 0x800800040d7bb
  | .l116f39 => 0x800800040d79b
  | .l116f67 => 0x800800040479b
  | .l116fbb => 0x8008000400799
  | .l116fd8 => 0x800800040279b
  | .l11700a => 0x8008000407f9f
  | .l117033 => 0x8008000402edf
  | .l117072 => 0x80080004007d3
  | .l117080 => 0x80080004007d7

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

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
