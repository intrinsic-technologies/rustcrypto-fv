import P256.Spec.Operations
import P256.Proofs.Projective.Algebra.Field.Polynomial


set_option autoImplicit false


namespace P256.Proofs.Projective.Algebra.FieldArithmetic
open P256.Spec.Operations (domain)

def cubicValue (x : Nat) : Nat :=
  (x * x * x + domain.a * x + domain.b) % domain.p

abbrev modulus := domain.p
abbrev constant := domain.p - domain.b

def frobeniusRemainder : Quadratic :=
  ⟨66434390973925144466073271287821796038003695194169110494110089305650096453661,
    12402202686218762177567235911775779164004716598278868847786114277539554646091,
    24678849118215552148312087830792888746041224110560601850711771001608500700145⟩

def frobeniusInverse : Quadratic :=
  ⟨76626890310466861426869089647039036757962535851890885406097439786770458211455,
    74462945259064871768191128030512052509059297803194871526163573358218695456204,
    34768139465301476436978405170953382516735956999154666452188405812258086013549⟩

set_option maxRecDepth 2048 in
theorem frobeniusRemainder_certificate :
    Quadratic.add modulus frobeniusRemainder Quadratic.indeterminate =
      Quadratic.pow modulus constant 3 Quadratic.indeterminate modulus := by
  decide +kernel

theorem frobeniusInverse_certificate :
    Quadratic.mul modulus constant 3 frobeniusRemainder frobeniusInverse = Quadratic.one := by
  decide +kernel

theorem cubic_relation {x : Nat} (h : cubicValue x = 0) :
    x * x * x % modulus = (constant + 3 * x) % modulus := by
  have ha : domain.a + 3 = modulus := by decide +kernel
  have hb : domain.b + constant = modulus := by decide +kernel
  have h₁ := Nat.add_mod_eq_add_mod_right (b := 0) (d := modulus) (3 * x) h
  simp only [Nat.zero_add] at h₁
  have he₁ : x * x * x + domain.a * x + domain.b + 3 * x =
      x * x * x + domain.b + modulus * x := by
    grind only
  rw [he₁, Nat.add_mul_mod_self_left] at h₁
  have h₂ := Nat.add_mod_eq_add_mod_right constant h₁
  have he₂ : x * x * x + domain.b + constant = x * x * x + modulus := by
    omega
  rw [he₂, Nat.add_mod_right] at h₂
  simpa only [Nat.add_comm] using h₂

theorem mod_eq_zero_of_add_mod_eq {p a b : Nat} (h : (a + b) % p = b % p) :
    a % p = 0 := by
  have hc : ((a : Int) + b) % p = (0 + (b : Int)) % p := by
    simpa only [Int.natCast_emod, Int.natCast_add, Int.zero_add] using congrArg (fun n : Nat => (n : Int)) h
  have hz := (Int.emod_add_cancel_right (b : Int)).mp hc
  apply Int.ofNat_inj.mp
  simpa only [Int.natCast_emod, Int.natCast_zero, Int.zero_emod] using hz

theorem no_root_of_fermat (x : Nat) (hfermat : x ^ modulus % modulus = x % modulus) :
    cubicValue x ≠ 0 := by
  intro hzero
  have hx := cubic_relation hzero
  have hf := congrArg (Quadratic.eval modulus x) frobeniusRemainder_certificate
  rw [Quadratic.eval_add, Quadratic.eval_pow _ _ _ _ _ _ hx,
    Quadratic.eval_indeterminate, ← Nat.pow_mod, hfermat] at hf
  have hr : Quadratic.eval modulus x frobeniusRemainder = 0 := by
    have hh := mod_eq_zero_of_add_mod_eq (p := modulus)
      (a := Quadratic.eval modulus x frobeniusRemainder) (b := x % modulus)
      (by simpa only [Nat.mod_mod] using hf)
    simpa only [Quadratic.eval, Nat.mod_mod] using hh
  have hi := congrArg (Quadratic.eval modulus x) frobeniusInverse_certificate
  rw [Quadratic.eval_mul _ _ _ _ _ _ hx, Quadratic.eval_one, hr, Nat.zero_mul,
    Nat.zero_mod] at hi
  have hp : 1 % modulus = 1 := by decide +kernel
  omega

end P256.Proofs.Projective.Algebra.FieldArithmetic
