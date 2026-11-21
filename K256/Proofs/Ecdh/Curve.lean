import K256.Proofs.Ecdh.Curve.Decode
import K256.Proofs.Ecdh.Curve.Scalar
import K256.Proofs.Ecdh.Curve.Cyclicity
import K256.Proofs.Ecdh.Curve.Endomorphism

set_option autoImplicit false

namespace K256.Proofs.Ecdh.Curve

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

def peerWindow (p : Curve.Point) (k : Nat) : Curve.Point :=
  let r := centered (splitFirst k)
  let s := centered (splitSecond k)
  signedWindow (signedBase r p) (signedBase s (endomorphism p)) 32 r.natAbs s.natAbs

private theorem signedBase_generatorMultiple (r a : Int) :
    signedBase r (generatorMultiple a) = generatorMultiple ((if r < 0 then -1 else 1) * a) := by
  unfold signedBase
  split <;> simp [generatorMultiple_neg]

private theorem abs_sign (r : Int) :
    (r.natAbs : Int) * (if r < 0 then -1 else 1) = r := by
  cases r with
  | ofNat n =>
    rw [ite_eq_right (show ¬ Int.ofNat n < 0 from Int.not_lt.mpr (Int.natCast_nonneg n)), Int.mul_one]
    rfl
  | negSucc n => simp; omega

theorem peerWindow_eq_scalarMul (p : Curve.Point) (hp : Curve.onCurve domain p = true)
    (k : Nat) (hk : k < domain.n) : peerWindow p k = Curve.scalarMul domain k p := by
  obtain ⟨a, rfl⟩ := exists_generatorMultiple p hp
  rw [peerWindow, endomorphism_generatorMultiple, signedBase_generatorMultiple,
    signedBase_generatorMultiple, signedWindow_multiple, scalarMul_generatorMultiple]
  simp only [← Int.mul_assoc, abs_sign, ← Int.add_mul]
  unfold generatorMultiple
  rw [Int.mul_emod, (split_correct k hk).1, Int.mul_emod (k : Int) a,
    Int.emod_eq_of_lt (Int.natCast_nonneg k) (Int.ofNat_lt.mpr hk)]

theorem scalarMul_infinity (k : Nat) : Curve.scalarMul domain k .infinity = .infinity := by
  rw [Group.scalarMul_eq_multiple domain Group.secp256k1_add_laws _ rfl]
  induction k with
  | zero => rfl
  | succ k ih => rw [Group.multiple, ih]; rfl

theorem peerWindow_ne_infinity (p : Curve.Point) (hp : Curve.onCurve domain p = true)
    (hne : p ≠ .infinity) (k : Nat) (hpos : 0 < k) (hk : k < domain.n) :
    peerWindow p k ≠ .infinity := by
  rw [peerWindow_eq_scalarMul p hp k hk]
  obtain ⟨a, ha⟩ := exists_generatorMultiple p hp
  let b := (a % (domain.n : Int)).toNat
  have hn : 0 < domain.n := by decide +kernel
  have hn' : (0 : Int) < domain.n := Int.ofNat_lt.mpr hn
  have hab : (b : Int) = a % (domain.n : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hn'))
  have hb : b < domain.n := Int.ofNat_lt.mp (hab ▸ Int.emod_lt_of_pos a hn')
  have hp' : p = generatorMultiple (b : Int) := by
    rw [ha, hab, generatorMultiple, generatorMultiple, Int.emod_emod]
  have hbpos : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hne
    rw [hp', hz]
    decide +kernel
  have hprod : 0 < k * b % domain.n := by
    apply Nat.pos_of_ne_zero
    intro hz
    rcases order_prime.dvd_mul (Nat.dvd_of_mod_eq_zero hz) with h | h
    · exact (Nat.not_le.mpr hk) (Nat.le_of_dvd hpos h)
    · exact (Nat.not_le.mpr hb) (Nat.le_of_dvd hbpos h)
  rw [hp', scalarMul_generatorMultiple, ← Int.natCast_mul, generatorMultiple,
    ← Int.natCast_emod, Int.toNat_natCast, ← generatorWindow_eq_scalarMul _ (Nat.mod_lt _ hn)]
  exact generatorWindow_ne_infinity _ hprod (Nat.mod_lt _ hn)

theorem sharedSecret_eq_x (secret peer : ByteArray) (p : Curve.Point) (k : Nat)
    (hs : Keys.decodeSecret domain secret = some k)
    (hp : K256.Spec.Secp256k1.groupPoint peer = some p) :
    K256.Spec.Secp256k1.sharedSecret secret peer =
      Encoding.natToOctets 32 (match Curve.scalarMul domain k p with
        | .infinity => 0 | .affine x _ => x) := by
  rw [K256.Spec.Secp256k1.sharedSecret, hp]
  cases p with
  | infinity =>
    rw [scalarMul_infinity]
    change (⟨Array.replicate 32 0⟩ : ByteArray) = Encoding.natToOctets 32 0
    decide +kernel
  | affine x y =>
    have hk : 0 < k ∧ k < domain.n := by
      dsimp only [Keys.decodeSecret] at hs
      split at hs
      · cases hs
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at *
        exact ⟨by omega, by omega⟩
      · cases hs
    have hc := groupPoint_onCurve _ _ hp
    have hne := peerWindow_ne_infinity (.affine x y) hc (by intro h; cases h) k hk.1 hk.2
    rw [peerWindow_eq_scalarMul _ hc _ hk.2] at hne
    simp only [Keys.sharedSecret, hs, Option.bind_some, Option.bind_eq_bind]
    cases hm : Curve.scalarMul domain k (.affine x y) with
    | infinity => exact False.elim (hne hm)
    | affine _ _ => rfl

end K256.Proofs.Ecdh.Curve
