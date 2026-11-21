import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords Projective)
open Generate.Curve

abbrev frameSp (sp : BitVec 64) := sp - 0x2b8

structure SavedFrame (initial : Registers) (sp tables : BitVec 64)
    (a : Registers) (m : Ram) : Prop where
  rsp : a[4] = ⟨64, frameSp sp⟩
  tableBase : a[3] = ⟨64, tables⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64
  control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → a[i] = initial[i]
  rbx : memLoad m (sp - 48) 64 = initial[3].get 64
  r12 : memLoad m (sp - 40) 64 = initial[12].get 64
  r13 : memLoad m (sp - 32) 64 = initial[13].get 64
  r14 : memLoad m (sp - 24) 64 = initial[14].get 64
  r15 : memLoad m (sp - 16) 64 = initial[15].get 64
  rbp : memLoad m (sp - 8) 64 = initial[5].get 64

abbrev first (k : Nat) := centered (splitFirst k)
abbrev second (k : Nat) := centered (splitSecond k)
abbrev signByte (v : Int) : BitVec 8 := if v < 0 then 1 else 0

structure SplitState (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (a : Registers) (m : Ram) : Prop extends SavedFrame initial sp tables a m where
  frame : RamWriteFrame original m [scratch sp 0x558]
  pointPtr : memLoad m (frameSp sp + 0x28) 64 = src
  digitPtr : memLoad m (frameSp sp + 0xd8) 64 = digits
  signFirst : a[14].get 8 = signByte (first k)
  signSecond : memLoad m (frameSp sp + 7) 8 = signByte (second k)
  firstWords : WordsAt m (frameSp sp + 0xe0) 64 (scalarWords (first k).natAbs)
  secondWords : WordsAt m (frameSp sp + 0xb0) 64 (scalarWords (second k).natAbs)

structure Recoded (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (a : Registers) (m : Ram) : Prop extends SavedFrame initial sp tables a m where
  frame : RamWriteFrame original m [scratch sp 0x558, ⟨digits.toNat, 544⟩]
  pointPtr : memLoad m (frameSp sp + 0x28) 64 = src
  digitPtr : a[5] = ⟨64, digits⟩
  signFirst : a[14].get 8 = signByte (first k)
  signSecond : memLoad m (frameSp sp + 7) 8 = signByte (second k)
  firstLength : memLoad m digits 64 = BitVec.ofNat 64 (Naf.digits (first k).natAbs).length
  secondLength : a[0] = ⟨64, BitVec.ofNat 64 (Naf.digits (second k).natAbs).length⟩
  firstBytes : DigitBytes m (digits + 8) (Naf.digits (first k).natAbs)
  secondBytes : DigitBytes m (digits + 0x118) (Naf.digits (second k).natAbs)

structure Bases (initial : Registers) (original : Ram) (sp tables digits : BitVec 64)
    (p : Curve.Point) (k : Nat) (a : Registers) (m : Ram) : Prop extends SavedFrame initial sp tables a m where
  frame : RamWriteFrame original m [scratch sp 0x558, ⟨digits.toNat, 544⟩]
  arguments : ParseSignature.ArgumentWidths a
  acc : a[14] = ⟨64, frameSp sp + 0x178⟩
  delta : a[15] = ⟨64, frameSp sp + 0x38⟩
  firstPoint : ∃ q : Projective, q.valid ∧ q.value = signedBase (first k) p ∧
    q.Stored m (frameSp sp + 0x178) ∧ q.double.Stored m (frameSp sp + 0x38)
  secondPoint : ∃ q : Projective, q.valid ∧ q.value = signedBase (second k) (endomorphism p) ∧
    q.Stored m (frameSp sp + 0x1f0)
  firstLength : memLoad m digits 64 = BitVec.ofNat 64 (Naf.digits (first k).natAbs).length
  secondLength : memLoad m (digits + 0x110) 64 = BitVec.ofNat 64 (Naf.digits (second k).natAbs).length
  firstBytes : DigitBytes m (digits + 8) (Naf.digits (first k).natAbs)
  secondBytes : DigitBytes m (digits + 0x118) (Naf.digits (second k).natAbs)

end K256.Proofs.Verify.Core.Lincomb.Prepare
