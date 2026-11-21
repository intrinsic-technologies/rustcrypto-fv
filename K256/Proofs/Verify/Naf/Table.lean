import K256.Proofs.Ecdh.Curve
import K256.Proofs.Verify.Naf.Arithmetic

namespace K256.Proofs.Verify.Naf

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

def oddTableEntry (p : Curve.Point) : Nat → Curve.Point
  | 0 => p
  | i+1 => Curve.add domain (oddTableEntry p i) (Curve.add domain p p)

private theorem oddTableEntry_multiple (a : Int) (i : Nat) :
    oddTableEntry (generatorMultiple a) i = generatorMultiple (((2 * i + 1 : Nat) : Int) * a) := by
  induction i with
  | zero => simp [oddTableEntry]
  | succ i ih =>
    rw [oddTableEntry, ih, generatorMultiple_add, generatorMultiple_add]
    congr 1
    push_cast
    grind only

theorem lookup_oddTableEntry (p : Curve.Point) (hp : Curve.onCurve domain p)
    {d : Int} (valid : ValidDigit d) (nz : d ≠ 0) :
    d.natAbs / 2 < 8 ∧
      (if d < 0 then Curve.neg domain (oddTableEntry p (d.natAbs / 2))
       else oddTableEntry p (d.natAbs / 2)) = selectDigit p d := by
  rcases valid with h | ⟨odd, lo, hi⟩
  · contradiction
  obtain ⟨a, rfl⟩ := Ecdh.Curve.exists_generatorMultiple p hp
  rw [oddTableEntry_multiple, selectDigit_multiple]
  have mag : 2 * (d.natAbs / 2) + 1 = d.natAbs := by cases d <;> omega
  rw [mag]
  constructor
  · cases d <;> omega
  · cases d with
    | ofNat k => rw [ite_eq_right (show ¬ Int.ofNat k < 0 from Int.not_lt.mpr (Int.natCast_nonneg k))]; rfl
    | negSucc k =>
      simp only [Int.negSucc_lt_zero, ite_true, generatorMultiple_neg, ← Int.neg_mul]
      rfl

end K256.Proofs.Verify.Naf
