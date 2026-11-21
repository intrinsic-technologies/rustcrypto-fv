import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l116d00
  | l1170b0
  | l1170c6
  | l1170d6
  | l1170db
  | l1170e3
  | l11715a
  | l117172
  | l11718a

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l116d00 : Label := .g0 .l116d00
@[match_pattern] abbrev Label.l1170b0 : Label := .g0 .l1170b0
@[match_pattern] abbrev Label.l1170c6 : Label := .g0 .l1170c6
@[match_pattern] abbrev Label.l1170d6 : Label := .g0 .l1170d6
@[match_pattern] abbrev Label.l1170db : Label := .g0 .l1170db
@[match_pattern] abbrev Label.l1170e3 : Label := .g0 .l1170e3
@[match_pattern] abbrev Label.l11715a : Label := .g0 .l11715a
@[match_pattern] abbrev Label.l117172 : Label := .g0 .l117172
@[match_pattern] abbrev Label.l11718a : Label := .g0 .l11718a

def Label.G0.address : Label.G0 → BitVec 64
  | .l116d00 => 0x111220
  | .l1170b0 => 0x1115d0
  | .l1170c6 => 0x1115e6
  | .l1170d6 => 0x1115f6
  | .l1170db => 0x1115fb
  | .l1170e3 => 0x111603
  | .l11715a => 0x11167a
  | .l117172 => 0x111692
  | .l11718a => 0x1116aa

def Label.G0.live : Label.G0 → Nat
  | .l116d00 => 0x800800040ffff
  | .l1170b0 => 0x800800040ffff
  | .l1170c6 => 0x800800040b038
  | .l1170d6 => 0x800800040b039
  | .l1170db => 0x800800040b039
  | .l1170e3 => 0x800800040b039
  | .l11715a => 0x8008000000000
  | .l117172 => 0x8008000000000
  | .l11718a => 0x8008000000000

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

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
