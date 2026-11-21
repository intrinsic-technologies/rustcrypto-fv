import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Common.Arithmetic.CubicNonzero.Polynomial

set_option autoImplicit false
open Standards.SECG.DomainParameters

namespace K256.Proofs.Common.Arithmetic

def decompressSquare (x : Nat) : Nat :=
  (x * x * x + Secp256k1.domain.a * x + Secp256k1.domain.b) % Secp256k1.domain.p

namespace CubicNonzero

abbrev modulus := Secp256k1.domain.p
abbrev constant := Secp256k1.domain.p - Secp256k1.domain.b

def frobeniusRemainder : Quadratic :=
  ⟨0,
    55594575648329892869085402983802832744385952214688224221778511981742606582253,
    0⟩

def frobeniusInverse : Quadratic :=
  ⟨0, 0, 46758632835564736012269203954919337884311706168562511263687580192619680188360⟩

set_option maxRecDepth 2048 in
theorem frobeniusRemainder_certificate :
    Quadratic.add modulus frobeniusRemainder Quadratic.indeterminate =
      Quadratic.pow modulus constant 0 Quadratic.indeterminate modulus := by
  decide +kernel

theorem frobeniusInverse_certificate :
    Quadratic.mul modulus constant 0 frobeniusRemainder frobeniusInverse = Quadratic.one := by
  decide +kernel

theorem cubic_relation {x : Nat} (h : decompressSquare x = 0) :
    x * x * x % modulus = constant % modulus := by
  have hb : Secp256k1.domain.b + constant = modulus := by decide +kernel
  have ha : Secp256k1.domain.a = 0 := rfl
  rw [decompressSquare, ha, Nat.zero_mul, Nat.add_zero] at h
  have h' := Nat.add_mod_eq_add_mod_right (b := 0) (d := modulus) constant h
  rw [Nat.add_assoc, hb, Nat.add_mod_right, Nat.zero_add] at h'
  exact h'

theorem mod_eq_zero_of_add_mod_eq {p a b : Nat} (h : (a + b) % p = b % p) :
    a % p = 0 := by
  have hc : ((a : Int) + b) % p = (0 + (b : Int)) % p := by
    simpa only [Int.natCast_emod, Int.natCast_add, Int.zero_add] using congrArg (fun n : Nat => (n : Int)) h
  have hz := (Int.emod_add_cancel_right (b : Int)).mp hc
  apply Int.ofNat_inj.mp
  simpa only [Int.natCast_emod, Int.natCast_zero, Int.zero_emod] using hz

theorem no_root_of_fermat (x : Nat) (hfermat : x ^ modulus % modulus = x % modulus) :
    decompressSquare x ≠ 0 := by
  intro hzero
  have hx : x * x * x % modulus = (constant + 0 * x) % modulus := by
    simpa only [Nat.add_zero, Nat.zero_mul] using cubic_relation hzero
  have hf := congrArg (Quadratic.eval modulus x) frobeniusRemainder_certificate
  rw [Quadratic.eval_add, Quadratic.eval_pow _ _ _ _ _ _ hx,
    Quadratic.eval_indeterminate, ← Nat.pow_mod, hfermat] at hf
  have hr : Quadratic.eval modulus x frobeniusRemainder = 0 := by
    have h := mod_eq_zero_of_add_mod_eq (p := modulus)
      (a := Quadratic.eval modulus x frobeniusRemainder) (b := x % modulus)
      (by simpa only [Nat.mod_mod] using hf)
    simpa only [Quadratic.eval, Nat.mod_mod] using h
  have hi := congrArg (Quadratic.eval modulus x) frobeniusInverse_certificate
  rw [Quadratic.eval_mul _ _ _ _ _ _ hx, Quadratic.eval_one, hr, Nat.zero_mul,
    Nat.zero_mod, show 1 % modulus = 1 by decide +kernel] at hi
  exact Nat.zero_ne_one hi

end CubicNonzero
end K256.Proofs.Common.Arithmetic
