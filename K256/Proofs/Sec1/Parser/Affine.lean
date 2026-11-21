import K256.Proofs.Common.Field.Repr
import K256.Proofs.Common.Refine.Store

namespace K256.Proofs.Sec1.Parser

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine K256.Proofs.Common.Field
open Standards.SECG.ECC

def AffineAt (mem : Ram) (p : BitVec 64) (x y : Fin modulus) (magnitude : Nat := 8) : Prop :=
  ∃ xl yl : Limbs, WordsAt mem p 64 xl ∧ WordsAt mem (p + 40) 64 yl ∧
    memLoad mem (p + 80) 8 = 0 ∧ FieldRepr xl x magnitude ∧ FieldRepr yl y magnitude

def PublicKeyAt (mem : Ram) (p : BitVec 64) (point : Curve.Point) : Prop :=
  ∃ x y : Fin modulus, point = .affine x.val y.val ∧ AffineAt mem p x y

theorem AffineAt.of_copy {m m' : Ram} {p p' : BitVec 64} {x y : Fin modulus} {mag : Nat}
    (h : AffineAt m p x y mag)
    (copy : ∀ off width : Nat, off + width / 8 ≤ 88 →
      memLoad m' (p' + BitVec.ofNat 64 off) width = memLoad m (p + BitVec.ofNat 64 off) width) :
    AffineAt m' p' x y mag := by
  obtain ⟨xl, yl, hx, hy, hflag, rx, ry⟩ := h
  refine ⟨xl, yl, ?_, ?_, (copy 80 8 (by decide)).trans hflag, rx, ry⟩
  · intro i hi
    exact (copy (8 * i) 64 (by omega)).trans (hx i hi)
  · intro i hi
    have c := copy (40 + 8 * i) 64 (by omega)
    have addr (a : BitVec 64) : wordAddr (a + 40) 64 i = a + BitVec.ofNat 64 (40 + 8 * i) := by
      rw [wordAddr, BitVec.add_assoc, BitVec.ofNat_add]
      rfl
    rw [← addr p', ← addr p] at c
    exact c.trans (hy i hi)

end K256.Proofs.Sec1.Parser
