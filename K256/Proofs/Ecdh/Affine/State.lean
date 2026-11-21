import K256.Proofs.Generate.Generator.Affine.State

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

structure CallState (l : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn10fe50.frameAt l fr)
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  source : Readable m fr.rsi 120
  dest : Writable Extracted.programImage m fr.rdi 88
  srcAddr : fr.rsi = fr.rsp + 352
  dstAddr : fr.rdi = fr.rsp + 4192
  high : fr.rsp.toNat + 4280 ≤ 2^32
  frame : RamWriteFrame fr.original m (writes fr)

def choiceBit (z : Fin modulus) : Word := if z.val = 0 then 0 else 1

def XAt (m : Ram) (p : Word) (point : Curve.Point) : Prop :=
  ∃ (v : Fin modulus) (w : Limbs), WordsAt m p 64 w ∧ FieldRepr w v 8 ∧
    v.val = match point with | .infinity => 0 | .affine x _ => x

def InverseAt (fr : Activation) (m : Ram) (z : Fin modulus) : Prop :=
  memLoad m (fr.rsp - 112) 8 = (choiceBit z).setWidth 8 ∧
  (z.val ≠ 0 → Inverted fr m z)

structure SelectionInput (fr : Activation) (a : Registers) (m : Ram) (x y z : Fin modulus) : Prop where
  address : a[12] = ⟨64, fr.rsp - 144⟩
  choice : a[15] = ⟨64, choiceBit z⟩
  pointAt : z.val ≠ 0 → XAt m (fr.rsp - 144) (toAffine x y z)

end K256.Proofs.Ecdh.Affine
