import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l1181a0
  | l1181ad
  | l1181e3
  | l11821e
  | l118251
  | l118288
  | l1182a7
  | l1182f8

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l1181a0 : Label := .g0 .l1181a0
@[match_pattern] abbrev Label.l1181ad : Label := .g0 .l1181ad
@[match_pattern] abbrev Label.l1181e3 : Label := .g0 .l1181e3
@[match_pattern] abbrev Label.l11821e : Label := .g0 .l11821e
@[match_pattern] abbrev Label.l118251 : Label := .g0 .l118251
@[match_pattern] abbrev Label.l118288 : Label := .g0 .l118288
@[match_pattern] abbrev Label.l1182a7 : Label := .g0 .l1182a7
@[match_pattern] abbrev Label.l1182f8 : Label := .g0 .l1182f8

def Label.G0.address : Label.G0 → BitVec 64
  | .l1181a0 => 0x1126c0
  | .l1181ad => 0x1126cd
  | .l1181e3 => 0x112703
  | .l11821e => 0x11273e
  | .l118251 => 0x112771
  | .l118288 => 0x1127a8
  | .l1182a7 => 0x1127c7
  | .l1182f8 => 0x112818

def Label.G0.live : Label.G0 → Nat
  | .l1181a0 => 0x800800040f0fe
  | .l1181ad => 0x80080004000f6
  | .l1181e3 => 0x8008000404ff7
  | .l11821e => 0x8008000404fff
  | .l118251 => 0x800800040cfff
  | .l118288 => 0x800800040cffd
  | .l1182a7 => 0x8008000408ffd
  | .l1182f8 => 0x80080004004f7

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

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
