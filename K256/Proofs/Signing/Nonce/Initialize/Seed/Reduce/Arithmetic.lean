import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.State

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

open Common.Invert.LinearCombination Common.Invert.ModularShift Generate.Generator.Multiply

theorem digestChoice {x : Nat} (bound : x < 2^256) :
    (if x < Secp256k1.domain.n then scalarWords x else words (digestDifference x).1) =
      scalarWords (x % Secp256k1.domain.n) ∧
    (digestDifference x).2 = (if x < Secp256k1.domain.n then 1 else 0) := by
  let d := digestDifference x
  have hd := subRaw_toNat (limbs (scalarWords x)) Split.Reduction.orderLimbs
  change d.2.toNat ≤ 1 ∧ d.1.toNat + Secp256k1.domain.n =
    Split.scalarValue (scalarWords x) + 2^256 * d.2.toNat at hd
  rw [Split.scalarWords_value x bound] at hd
  have small := limbs_toNat_lt d.1
  have order : 2^256 < 2 * Secp256k1.domain.n := by decide +kernel
  have bit := eq_zero_or_one hd.1
  change (if _ then _ else words d.1) = _ ∧ d.2 = _
  rcases bit with hb | hb <;> rw [hb] at hd ⊢
  · change _ ≤ _ ∧ d.1.toNat + Secp256k1.domain.n = x + 2^256 * 0 at hd
    have hx : ¬ x < Secp256k1.domain.n := by omega
    rw [ite_eq_right hx,ite_eq_right hx,Split.Addition.limbWords_eq,Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact ⟨congrArg scalarWords (by omega),rfl⟩
  · change _ ≤ _ ∧ d.1.toNat + Secp256k1.domain.n = x + 2^256 * 1 at hd
    have hx : x < Secp256k1.domain.n := by omega
    rw [ite_eq_left hx,ite_eq_left hx,Nat.mod_eq_of_lt hx]
    exact ⟨rfl,rfl⟩

end K256.Proofs.Signing.Nonce.Initialize
