import K256.Proofs.Signing.Nonce.Fill.State
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Invert.LinearCombination.Wide

namespace K256.Proofs.Signing.Nonce.Fill

open Prelude Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Common.Invert.LinearCombination
open Generate.Generator.Multiply
open Generate.Generator.Multiply.Split
open Initialize (State)

private theorem foldOctetsBound (bytes : List UInt8) (initial limit : Nat)
    (bound : initial < limit) :
    bytes.foldl (fun value byte => 256 * value + byte.toNat) initial <
      256 ^ bytes.length * limit := by
  induction bytes generalizing initial limit with
  | nil =>
    simpa only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.one_mul] using bound
  | cons byte bytes ih =>
    rw [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.mul_assoc]
    have byteBound := byte.toNat_lt
    exact ih _ _ (by omega)

theorem candidateBound (state : State) : (candidate state).1 < 2^256 := by
  rw [Drbg.candidate_eq]
  have sz : (Drbg.updateValue state).value.size = 32 := Vector.size_toArray _
  have bound := foldOctetsBound (Drbg.updateValue state).value.data.toList 0 1 Nat.zero_lt_one
  simpa only [Encoding.octetsToNat, Array.foldl_toList, Array.length_toList, ByteArray.size_data,
    Nat.mul_one, sz, show 256^32 = 2^256 by decide +kernel] using bound

abbrev nonceLimbs (k : Nat) : Limbs :=
  let w := scalarWords k
  ⟨w[0], w[1], w[2], w[3]⟩

theorem nonceLimbs_value (k : Nat) (bound : k < 2^256) :
    (nonceLimbs k).toNat = k := scalarWords_value k bound

theorem nonceLimbs_zero {k : Nat} (bound : k < 2^256) :
    (∀ i (hi : i < 4), (scalarWords k)[i] = 0) ↔ k = 0 := by
  constructor
  · intro h
    have eq := nonceLimbs_value k bound
    change (scalarWords k)[0].toNat + 2^64 * ((scalarWords k)[1].toNat + 2^64 *
      ((scalarWords k)[2].toNat + 2^64 * (scalarWords k)[3].toNat)) = k at eq
    rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)] at eq
    exact eq.symm
  · rintro rfl i hi
    simp only [scalarWords, Vector.getElem_ofFn, Nat.zero_div]
    rfl

theorem nonceOrderFlag (k : Nat) (bound : k < 2^256) :
    (subRaw (nonceLimbs k) (nonceLimbs domain.n)).2 = if k < domain.n then 1 else 0 := by
  let p := subRaw (nonceLimbs k) (nonceLimbs domain.n)
  have h := subRaw_toNat (nonceLimbs k) (nonceLimbs domain.n)
  rw [nonceLimbs_value k bound, nonceLimbs_value domain.n (by decide +kernel)] at h
  have h0 := p.1.l0.isLt
  have h1 := p.1.l1.isLt
  have h2 := p.1.l2.isLt
  have h3 := p.1.l3.isLt
  change p.2.toNat ≤ 1 ∧ p.1.toNat + domain.n = k + 2^256 * p.2.toNat at h
  have small : p.1.toNat < 2^256 := by simp only [Limbs.toNat, Nat.reducePow]; omega
  change p.2 = _
  rcases eq_zero_or_one h.1 with z | o
  · have ge : ¬ k < domain.n := by
      have eq := h.2
      rw [z] at eq
      change p.1.toNat + domain.n = k + 2^256 * 0 at eq
      omega
    rw [ite_eq_right ge, z]
  · have lt : k < domain.n := by
      have eq := h.2
      rw [o] at eq
      change p.1.toNat + domain.n = k + 2^256 * 1 at eq
      omega
    rw [ite_eq_left lt, o]

theorem subWord_reassoc (a b c : BitVec 64) :
    (0#64 - c).sshiftRight 63 + a - b = subWord a b c := by
  simp only [subWord, BitVec.zero_sub]
  bv_omega

end K256.Proofs.Signing.Nonce.Fill
