import K256.Proofs.Verify.Core.Lincomb.Prepare.State

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

structure SignedFrame (initial : Registers) (original : Ram) (sp tables digits : BitVec 64)
    (k : Nat) (a : Registers) (m : Ram) : Prop extends SavedFrame initial sp tables a m where
  frame : RamWriteFrame original m [scratch sp 0x558, ⟨digits.toNat, 544⟩]
  firstLength : memLoad m digits 64 = BitVec.ofNat 64 (Naf.digits (first k).natAbs).length
  secondLength : memLoad m (digits + 0x110) 64 = BitVec.ofNat 64 (Naf.digits (second k).natAbs).length
  firstBytes : DigitBytes m (digits + 8) (Naf.digits (first k).natAbs)
  secondBytes : DigitBytes m (digits + 0x118) (Naf.digits (second k).natAbs)

def PointValueAt (m : Ram) (ptr : BitVec 64) (value : Curve.Point) : Prop :=
  ∃ p : Projective, p.valid ∧ p.value = value ∧ p.Stored m ptr

structure FirstBase (initial : Registers) (original : Ram) (sp tables digits : BitVec 64)
    (p : Curve.Point) (k : Nat) (a : Registers) (m : Ram) : Prop extends SignedFrame initial original sp tables digits k a m where
  point : PointValueAt m (frameSp sp + 0x178) (signedBase (first k) p)
  sign : memLoad m (frameSp sp + 7) 8 = signByte (second k)
  fold : a[5] = ⟨64, 0x1000003d1⟩
  negTop : a[12] = ⟨64, 0x3fffffffffffc⟩
  negMiddle : a[13] = ⟨64, 0x3ffffffffffffc⟩
  maskTop : a[14] = ⟨64, 0xffffffffffff⟩
  maskMiddle : a[15] = ⟨64, 0xfffffffffffff⟩

structure SignedPair (initial : Registers) (original : Ram) (sp tables digits : BitVec 64)
    (p : Curve.Point) (k : Nat) (a : Registers) (m : Ram) : Prop extends SignedFrame initial original sp tables digits k a m where
  firstPoint : PointValueAt m (frameSp sp + 0x178) (signedBase (first k) p)
  secondPoint : PointValueAt m (frameSp sp + 0x1f0) (signedBase (second k) (endomorphism p))

end K256.Proofs.Verify.Core.Lincomb.Prepare
