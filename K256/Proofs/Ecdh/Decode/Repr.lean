import K256.Proofs.Sec1.Parser.Affine

namespace K256.Proofs.Ecdh.Decode

open X86.Machine X86Proofs K256.Proofs.Refine Standards.SECG.ECC

def AffinePointAt (mem : Ram) (base : BitVec 64) : Curve.Point → Prop
  | .infinity => memLoad mem (base + 80) 8 = 1
  | .affine x y => ∃ a b : Fin Common.Field.modulus,
      x = a.val ∧ y = b.val ∧ Sec1.Parser.AffineAt mem base a b 1

theorem AffinePointAt.of_copy {m m' : Ram} {p p' : BitVec 64} {point : Curve.Point}
    (h : AffinePointAt m p point)
    (copy : ∀ off width : Nat, off + width / 8 ≤ 88 →
      memLoad m' (p' + BitVec.ofNat 64 off) width = memLoad m (p + BitVec.ofNat 64 off) width) :
    AffinePointAt m' p' point := by
  cases point with
  | infinity => exact (copy 80 8 (by decide)).trans h
  | affine x y =>
    obtain ⟨a,b,hx,hy,atPoint⟩ := h
    exact ⟨a,b,hx,hy,atPoint.of_copy copy⟩

end K256.Proofs.Ecdh.Decode
