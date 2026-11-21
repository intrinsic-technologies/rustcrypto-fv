import P256.Proofs.Projective.Multiply.Arithmetic
import P256.Proofs.Projective.Multiply.Table
import P256.Proofs.Projective.Multiply.Lookup.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ScalarMul

open P256.Spec.Operations (domain)
open Algebra
open Standards.SECG.ECC Group ProjectiveLookup

theorem tableEntry_correct (laws : CurveAddLaws domain)
    (point : Projective) (hpoint : point.valid) (i : Nat) :
    (point.tableEntry i).valid ∧ (point.tableEntry i).toAffine =
      multiple domain point.toAffine (i + 1) := by
  induction i with
  | zero => exact ⟨hpoint, rfl⟩
  | succ i ih =>
    refine ⟨Projective.add_valid point _ hpoint ih.1, ?_⟩
    change (point.add (point.tableEntry i)).toAffine = _
    have he := add_multiple_toAffine laws point.toAffine (Projective.toAffine_onCurve point hpoint)
      point (point.tableEntry i) hpoint ih.1 1 (i + 1) rfl ih.2
    simpa only [Nat.add_comm 1] using he

theorem selectMagnitude_correct (laws : CurveAddLaws domain)
    (point : Projective) (hpoint : point.valid) (m : Nat) (hm : m ≤ 8) :
    (selectMagnitude (Projective.table point) m).valid ∧
      (selectMagnitude (Projective.table point) m).toAffine =
        multiple domain point.toAffine m := by
  by_cases hzero : m = 0
  · subst m
    rw [selectMagnitude_zero]
    exact ⟨Projective.identity_valid, rfl⟩
  · have hpos : 0 < m ∧ m ≤ 8 := by omega
    simp only [selectMagnitude, dite_eq_left hpos, Projective.table]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using
      tableEntry_correct laws point hpoint (m - 1)

theorem add_signedLookup_correct (laws : CurveAddLaws domain)
    (point acc : Projective) (hpoint : point.valid) (hacc : acc.valid)
    (m n : Nat) (hacc_eq : acc.toAffine = multiple domain point.toAffine m)
    (digit : BitVec 8) (hbound : -8 ≤ digit.toInt ∧ digit.toInt ≤ 8)
    (hvalue : (m : Int) + digit.toInt = n) :
    (acc.add (signedLookup (Projective.table point) digit)).valid ∧
      (acc.add (signedLookup (Projective.table point) digit)).toAffine =
        multiple domain point.toAffine n := by
  have hb := Projective.toAffine_onCurve point hpoint
  have hmagnitude : digitMagnitude digit ≤ 8 := by
    rw [digitMagnitude_eq_natAbs]
    omega
  have hlookup := selectMagnitude_correct laws point hpoint (digitMagnitude digit) hmagnitude
  have hmagnitude_eq := digitMagnitude_eq_natAbs digit
  unfold signedLookup
  cases hsign : digit.msb with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hnonneg := BitVec.toInt_nonneg_of_msb_false hsign
    have habs := Int.natAbs_of_nonneg hnonneg
    have hsum : m + digitMagnitude digit = n := by omega
    refine ⟨Projective.add_valid acc _ hacc hlookup.1, ?_⟩
    rw [add_multiple_toAffine laws point.toAffine hb acc _ hacc hlookup.1
      m (digitMagnitude digit) hacc_eq hlookup.2, hsum]
  | true =>
    simp only [ite_true]
    have hnegative := BitVec.toInt_neg_of_msb_true hsign
    have habs := Int.ofNat_natAbs_of_nonpos (by omega : digit.toInt ≤ 0)
    have hle : digitMagnitude digit ≤ m := by omega
    have hsub : m - digitMagnitude digit = n := by omega
    refine ⟨Projective.add_valid acc _ hacc (Projective.negate_valid _ hlookup.1), ?_⟩
    rw [add_negate_multiple_toAffine laws point.toAffine hb acc _ hacc hlookup.1
      m (digitMagnitude digit) hle hacc_eq hlookup.2, hsub]

end P256.Proofs.Projective.Multiply.ScalarMul
