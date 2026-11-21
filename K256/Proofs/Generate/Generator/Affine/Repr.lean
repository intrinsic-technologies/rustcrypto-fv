import K256.Proofs.Sec1.Parser.Affine
import K256.Proofs.Common.Field.PowMod

namespace K256.Proofs.Generate.Generator.Affine

open X86Proofs X86.Machine K256.Proofs.Common.Field K256.Proofs.Refine
open Standards.SECG.ECC

def inverse (z : Fin modulus) : Fin modulus :=
  ⟨Curve.inverse modulus z.val, by
    rw [Curve.inverse, PowMod.powMod_eq_pow_mod]
    exact Nat.mod_lt _ (by decide)⟩

def toAffine (x y z : Fin modulus) : Curve.Point :=
  if z.val = 0 then .infinity else .affine (x * inverse z).val (y * inverse z).val

def ProjectiveAt (mem : Ram) (base : Word) (point : Curve.Point) : Prop :=
  ∃ (x y z : Fin modulus) (xl yl zl : Limbs),
    WordsAt mem base 64 xl ∧ WordsAt mem (base + 40) 64 yl ∧
    WordsAt mem (base + 80) 64 zl ∧ FieldRepr xl x 8 ∧ FieldRepr yl y 8 ∧
    FieldRepr zl z 8 ∧ point = toAffine x y z

theorem publicKeyAt_of_products {mem : Ram} {base : Word}
    {x y z : Fin modulus} {point : Curve.Point} {xl yl : Limbs}
    (hp : point = toAffine x y z) (hne : point ≠ .infinity)
    (wx : WordsAt mem base 64 xl) (wy : WordsAt mem (base + 40) 64 yl)
    (flag : memLoad mem (base + 80) 8 = 0)
    (hx : FieldRepr xl (x * inverse z) 8) (hy : FieldRepr yl (y * inverse z) 8) :
    K256.Proofs.Sec1.Parser.PublicKeyAt mem base point := by
  unfold toAffine at hp
  split at hp
  · exact (hne hp).elim
  · exact ⟨_, _, hp, _, _, wx, wy, flag, hx, hy⟩

end K256.Proofs.Generate.Generator.Affine
