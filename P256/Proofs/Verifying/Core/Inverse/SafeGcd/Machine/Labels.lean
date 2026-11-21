import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Spec.Program.Extracted.Sections
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

inductive Label.G0 where
  | l1170b0
  | l1171a0
  | l1141e0
  | l114201
  | l114285
  | l1142ec
  | l114300
  | l114311
  | l11435c
  | l1143a7
  | l11441c
  | l11446c
  | l1144b3
  | l11453e
  | l11454e
  | l114558
  | l114560
  | l114568
  | l114574
  | l1145af
  | l1145da
  | l1145e2
  | l114616
  | l114630
  | l114635
  | l11465b
  | l114675
  | l11467a
  | l114680
  | l11468d
  | l114698
  | l1146d9
  | l1181a0

inductive Label where
  | g0 (l : Label.G0)

@[match_pattern] abbrev Label.l1170b0 : Label := .g0 .l1170b0
@[match_pattern] abbrev Label.l1171a0 : Label := .g0 .l1171a0
@[match_pattern] abbrev Label.l1141e0 : Label := .g0 .l1141e0
@[match_pattern] abbrev Label.l114201 : Label := .g0 .l114201
@[match_pattern] abbrev Label.l114285 : Label := .g0 .l114285
@[match_pattern] abbrev Label.l1142ec : Label := .g0 .l1142ec
@[match_pattern] abbrev Label.l114300 : Label := .g0 .l114300
@[match_pattern] abbrev Label.l114311 : Label := .g0 .l114311
@[match_pattern] abbrev Label.l11435c : Label := .g0 .l11435c
@[match_pattern] abbrev Label.l1143a7 : Label := .g0 .l1143a7
@[match_pattern] abbrev Label.l11441c : Label := .g0 .l11441c
@[match_pattern] abbrev Label.l11446c : Label := .g0 .l11446c
@[match_pattern] abbrev Label.l1144b3 : Label := .g0 .l1144b3
@[match_pattern] abbrev Label.l11453e : Label := .g0 .l11453e
@[match_pattern] abbrev Label.l11454e : Label := .g0 .l11454e
@[match_pattern] abbrev Label.l114558 : Label := .g0 .l114558
@[match_pattern] abbrev Label.l114560 : Label := .g0 .l114560
@[match_pattern] abbrev Label.l114568 : Label := .g0 .l114568
@[match_pattern] abbrev Label.l114574 : Label := .g0 .l114574
@[match_pattern] abbrev Label.l1145af : Label := .g0 .l1145af
@[match_pattern] abbrev Label.l1145da : Label := .g0 .l1145da
@[match_pattern] abbrev Label.l1145e2 : Label := .g0 .l1145e2
@[match_pattern] abbrev Label.l114616 : Label := .g0 .l114616
@[match_pattern] abbrev Label.l114630 : Label := .g0 .l114630
@[match_pattern] abbrev Label.l114635 : Label := .g0 .l114635
@[match_pattern] abbrev Label.l11465b : Label := .g0 .l11465b
@[match_pattern] abbrev Label.l114675 : Label := .g0 .l114675
@[match_pattern] abbrev Label.l11467a : Label := .g0 .l11467a
@[match_pattern] abbrev Label.l114680 : Label := .g0 .l114680
@[match_pattern] abbrev Label.l11468d : Label := .g0 .l11468d
@[match_pattern] abbrev Label.l114698 : Label := .g0 .l114698
@[match_pattern] abbrev Label.l1146d9 : Label := .g0 .l1146d9
@[match_pattern] abbrev Label.l1181a0 : Label := .g0 .l1181a0

def Label.G0.address : Label.G0 → BitVec 64
  | .l1170b0 => 0x1115d0
  | .l1171a0 => 0x1116c0
  | .l1141e0 => 0x112190
  | .l114201 => 0x1121b1
  | .l114285 => 0x112235
  | .l1142ec => 0x11229c
  | .l114300 => 0x1122b0
  | .l114311 => 0x1122c1
  | .l11435c => 0x11230c
  | .l1143a7 => 0x112357
  | .l11441c => 0x1123cc
  | .l11446c => 0x11241c
  | .l1144b3 => 0x112463
  | .l11453e => 0x1124ee
  | .l11454e => 0x1124fe
  | .l114558 => 0x112508
  | .l114560 => 0x112510
  | .l114568 => 0x112518
  | .l114574 => 0x112524
  | .l1145af => 0x11255f
  | .l1145da => 0x11258a
  | .l1145e2 => 0x112592
  | .l114616 => 0x1125c6
  | .l114630 => 0x1125e0
  | .l114635 => 0x1125e5
  | .l11465b => 0x11260b
  | .l114675 => 0x112625
  | .l11467a => 0x11262a
  | .l114680 => 0x112630
  | .l11468d => 0x11263d
  | .l114698 => 0x112648
  | .l1146d9 => 0x112689
  | .l1181a0 => 0x1126c0

def Label.G0.live : Label.G0 → Nat
  | .l1170b0 => 0x800800040ffff
  | .l1171a0 => 0x800800040ffff
  | .l1141e0 => 0x800800040ffff
  | .l114201 => 0x800800040af7c
  | .l114285 => 0x800800040af38
  | .l1142ec => 0x800800040af38
  | .l114300 => 0x800800040be10
  | .l114311 => 0x800800040fe18
  | .l11435c => 0x800800040fc38
  | .l1143a7 => 0x800800040fc38
  | .l11441c => 0x800800040fc38
  | .l11446c => 0x800800040fc38
  | .l1144b3 => 0x800800040bf38
  | .l11453e => 0x800800040bf38
  | .l11454e => 0x800800040bf78
  | .l114558 => 0x800800040bf7c
  | .l114560 => 0x800800040bf7c
  | .l114568 => 0x800800040bf7c
  | .l114574 => 0x800800040bc54
  | .l1145af => 0x800800048be14
  | .l1145da => 0x8008000409e55
  | .l1145e2 => 0x8008000409e57
  | .l114616 => 0x8008000409e53
  | .l114630 => 0x8008000409edf
  | .l114635 => 0x8008000409edf
  | .l11465b => 0x800800040ff1d
  | .l114675 => 0x8008000409edf
  | .l11467a => 0x8008000409edf
  | .l114680 => 0x8008000409edf
  | .l11468d => 0x8008000409edf
  | .l114698 => 0x800800040bf38
  | .l1146d9 => 0x8008000404f1c
  | .l1181a0 => 0x800800040ffff

def address : Label → BitVec 64
  | .g0 l => l.address

def live : Label → Nat
  | .g0 l => l.live

def retLive : Nat := 0x800800040ff3d

def textSection : Prelude.ImageSection :=
  ⟨P256.Spec.Program.Extracted.textAddress, P256.Spec.Program.Extracted.textBytes⟩

def sections : Prelude.ImageSections :=
  [textSection]

def fnCode : CodeMap := sections.toCodeMap

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
