import K256.Proofs.Generate.Generator.Multiply.Records
import K256.Proofs.Generate.Generator.Multiply.Radix.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

abbrev firstComponent (d : Nat) := Curve.centered (Curve.splitFirst d)
abbrev secondComponent (d : Nat) := Curve.centered (Curve.splitSecond d)
abbrev firstBase (d : Nat) := Curve.signedBase (firstComponent d) domain.G
abbrev secondBase (d : Nat) := Curve.signedBase (secondComponent d) (Curve.endomorphism domain.G)

structure Prepared (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d748 fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  frame : RamWriteFrame fr.original m (coreWrites fr)
  firstTable : TableAt m fr.rcx (firstBase d)
  secondTable : TableAt m (fr.rcx + 960) (secondBase d)
  firstDigits : WordsAt m fr.r9 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val)
  secondDigits : WordsAt m (fr.r9 + 33) 8
    (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val)
  accumulator : ∃ p : Projective, p.valid ∧ p.Stored m (fr.rsp - 0xb90) ∧
    p.value = Curve.signedWindow (firstBase d) (secondBase d) 0
      (Curve.radixRemaining (firstComponent d).natAbs 32) (Curve.radixRemaining (secondComponent d).natAbs 32)
  locals :
    let sp := fr.rsp - 0xcb8
    ∀ kv ∈ ([(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),(0x248,fr.rdi),(0xcc0,1)] :
      List (BitVec 64 × BitVec 64)), memLoad m (sp + kv.1) 64 = kv.2


namespace Prepare

abbrev sp (fr : Activation) := fr.rsp - 0xcb8

def Locals (fr : Activation) (m : Ram) (kvs : List (BitVec 64 × BitVec 64)) : Prop :=
  ∀ kv ∈ kvs, memLoad m (sp fr + kv.1) 64 = kv.2

structure State (l : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt l fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  frame : RamWriteFrame fr.original m (coreWrites fr)
  locals : Locals fr m [(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),(0x248,fr.rdi),(0xcc0,1)]

structure Magnitudes (fr : Activation) (m : Ram) (d : Nat) : Prop where
  first : WordsAt m (sp fr + 0x270) 64 (scalarWords (firstComponent d).natAbs)
  second : WordsAt m (sp fr + 0x290) 64 (scalarWords (secondComponent d).natAbs)

structure BasesReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop
    extends State .l11cf0d fr a m, Magnitudes fr m d where
  extra : Locals fr m [(0x8,0),(0x60,66),(0x68,152),(0x88,152),(0xc0,0),(0xd8,fr.rcx)]
  firstBaseStored : ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x328) ∧ p.value = firstBase d
  endomorphismStored : ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x2b0) ∧ p.value = Curve.endomorphism domain.G
  sign : memLoad m (sp fr + 0x48) 8 = if secondComponent d < 0 then 1 else 0
  mask4 : a[3] = ⟨64,0x3ffffffffffffc⟩
  mask52 : a[12] = ⟨64,0xfffffffffffff⟩
  mask48 : a[14] = ⟨64,0xffffffffffff⟩
  basePtr : a[5] = ⟨64,sp fr + 0x328⟩
  workPtr : a[15] = ⟨64,sp fr + 0x1d0⟩

structure Tables (fr : Activation) (m : Ram) (d : Nat) : Prop where
  firstTable : TableAt m fr.rcx (firstBase d)
  secondTable : TableAt m (fr.rcx + 960) (secondBase d)

structure TablesReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop
    extends State .l11d546 fr a m, Magnitudes fr m d, Tables fr m d where
  extra : Locals fr m [(0x60,66),(0x88,152),(0xc0,0)]
  index : a[14] = ⟨64,0⟩
  tablePtr : a[5] = ⟨64,fr.rcx⟩
  firstDigitPtr : a[12] = ⟨64,sp fr + 0x128⟩
  secondDigitPtr : a[15] = ⟨64,sp fr + 0x1d0⟩

structure DigitsReady (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop
    extends State .l11d620 fr a m, Tables fr m d where
  digitCount : memLoad m (sp fr + 0x60) 64 = 66
  firstDigits : WordsAt m fr.r9 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val)
  secondDigits : WordsAt m (fr.r9 + 33) 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val)

end Prepare

end K256.Proofs.Generate.Generator.Multiply
