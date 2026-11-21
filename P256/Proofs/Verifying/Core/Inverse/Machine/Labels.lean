import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Verifying.Core.Inverse.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l115020
  | l11504a
  | l115076
  | l1141e0
  | l1234c0

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l115020 : Label := .g0 .l115020
@[match_pattern] abbrev Label.l11504a : Label := .g0 .l11504a
@[match_pattern] abbrev Label.l115076 : Label := .g0 .l115076
@[match_pattern] abbrev Label.l1141e0 : Label := .g0 .l1141e0
@[match_pattern] abbrev Label.l1234c0 : Label := .g0 .l1234c0

def Label.G0.address : Label.G0 → BitVec 64
  | .l115020 => 0x112fd0
  | .l11504a => 0x112ffa
  | .l115076 => 0x113026
  | .l1141e0 => 0x112190
  | .l1234c0 => 0x119070

def Label.G0.live : Label.G0 → Nat
  | .l115020 => 0x800800040ffff
  | .l11504a => 0x800800040f03c
  | .l115076 => 0x800800040f03d
  | .l1141e0 => 0x800800040ffff
  | .l1234c0 => 0x800800040f0bc

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

end P256.Proofs.Verifying.Core.Inverse.Machine
