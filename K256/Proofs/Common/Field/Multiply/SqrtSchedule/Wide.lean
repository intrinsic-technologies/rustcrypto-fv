import K256.Proofs.Common.Field.Multiply.Bounds

namespace K256.Proofs.Common.Field.Multiply.SqrtSchedule
open X86Proofs

private theorem wideValue_inj {a b : Wide} (h : wideValue a = wideValue b) : a = b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · have ea := SquareValue.lo_toNat a.1 a.2
    have eb := SquareValue.lo_toNat b.1 b.2
    exact ea.trans ((congrArg (· % 2^64) h).trans eb.symm)
  · have al := a.1.isLt
    have bl := b.1.isLt
    simp only [wideValue, pairNat] at h
    omega

private theorem wideValue_add (a b : Wide) :
    wideValue (wideAdd a b) = (wideValue a + wideValue b) % 2^128 := by
  have hc := SquareValue.cf_toNat a.1 b.1
  have al := a.1.isLt
  have bl := b.1.isLt
  have ah := a.2.isLt
  have bh := b.2.isLt
  change pairNat (a.1 + b.1) (a.2 + b.2 + SquareValue.cf a.1 b.1) = _
  simp only [wideValue, pairNat, BitVec.toNat_add]
  omega

theorem wideAddRev_eq (a b : Wide) : wideAddRev a b = wideAdd a b := by
  simp only [wideAddRev, wideAdd, BitVec.add_comm b.2 a.2]

theorem wideAdd_comm (a b : Wide) : wideAdd a b = wideAdd b a := by
  apply wideValue_inj
  simp only [wideValue_add, Nat.add_comm (wideValue a) (wideValue b)]

theorem wideAdd_assoc (a b c : Wide) :
    wideAdd (wideAdd a b) c = wideAdd a (wideAdd b c) := by
  apply wideValue_inj
  simp only [wideValue_add, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem wideAdd_left_comm (a b c : Wide) :
    wideAdd a (wideAdd b c) = wideAdd b (wideAdd a c) := by
  rw [← wideAdd_assoc, wideAdd_comm a b, wideAdd_assoc]

theorem wideMul_comm (a b : Word) : wideMul a b = wideMul b a := by
  apply wideValue_inj
  exact (SquareValue.pair_mul a b).trans ((Nat.mul_comm _ _).trans (SquareValue.pair_mul b a).symm)

end K256.Proofs.Common.Field.Multiply.SqrtSchedule
