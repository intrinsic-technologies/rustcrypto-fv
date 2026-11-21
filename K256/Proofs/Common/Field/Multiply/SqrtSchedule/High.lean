import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Wide
import X86Proofs.Instructions.Shrd.Operation
import X86Proofs.Core.Bits

namespace K256.Proofs.Common.Field.Multiply.SqrtSchedule
open X86Proofs

theorem shrd52_eq (lo hi : Word) : shrdResult 52 lo hi = shldResult 12 hi lo := by
  change lo >>> 52 ||| hi <<< 12 = hi <<< 12 ||| lo >>> 52
  exact BitVec.or_comm _ _

theorem top_product_shift_zero {u v : Word} (h : u.toNat * v.toNat < 2^116) :
    (wideMul u v).2 >>> 52 = 0 := by
  have hp := SquareValue.pair_mul u v
  unfold pairNat at hp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (mulResult u v).2.toNat / 2^52 = 0
  omega

theorem top_product_lt {a b : Limbs} {x y : Fin modulus}
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    a[4].toNat * b[4].toNat < 2^116 := by
  have ha₄ : a[4].toNat ≤ 16 * (2^48-1) := ha.1 ⟨4, by decide⟩
  have hb₄ : b[4].toNat ≤ 16 * (2^48-1) := hb.1 ⟨4, by decide⟩
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul ha₄ hb₄) (by decide)

def scaleHigh (q : Wide) (lo : Word) : Wide :=
  let product := wideMul lo 0x1000003d10
  (product.1, (q.2 >>> 52) * (0x1000003d10 : Word) + product.2)

theorem scaleHigh_eq {q : Wide} (h : q.2 >>> 52 = 0) (lo : Word) :
    scaleHigh q lo = wideMul lo 0x1000003d10 := by
  simp only [scaleHigh, h]
  change (_, (0 : Word) + (wideMul lo 0x1000003d10).2) = _
  exact Prod.ext rfl (BitVec.zero_add _)

end K256.Proofs.Common.Field.Multiply.SqrtSchedule
