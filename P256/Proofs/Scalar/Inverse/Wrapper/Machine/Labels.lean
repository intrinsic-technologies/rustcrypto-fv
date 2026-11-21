import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Scalar.Inverse.Wrapper.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l118910
  | l11893a
  | l118966
  | l117650
  | l126f60

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l118910 : Label := .g0 .l118910
@[match_pattern] abbrev Label.l11893a : Label := .g0 .l11893a
@[match_pattern] abbrev Label.l118966 : Label := .g0 .l118966
@[match_pattern] abbrev Label.l117650 : Label := .g0 .l117650
@[match_pattern] abbrev Label.l126f60 : Label := .g0 .l126f60

def Label.G0.address : Label.G0 → BitVec 64
  | .l118910 => 0x112e30
  | .l11893a => 0x112e5a
  | .l118966 => 0x112e86
  | .l117650 => 0x111b70
  | .l126f60 => 0x119070

def Label.G0.live : Label.G0 → Nat
  | .l118910 => 0x800800040ffff
  | .l11893a => 0x800800040f03c
  | .l118966 => 0x800800040f03d
  | .l117650 => 0x800800040ffff
  | .l126f60 => 0x800800040f0bc

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

end P256.Proofs.Scalar.Inverse.Wrapper.Machine
