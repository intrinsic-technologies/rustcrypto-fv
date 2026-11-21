import K256.Proofs.Generate.Curve.Decompose
import K256.Proofs.Generate.Curve.OrderPrime
import K256.Proofs.Generate.Curve.Window
import Standards.SECG.ECC.Keys

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve

open Standards.SECG.ECC
open Standards.SECG.DomainParameters.Secp256k1

def endomorphism : Curve.Point → Curve.Point
  | .infinity => .infinity
  | .affine x y =>
    .affine (x * 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee % domain.p) y

theorem endomorphism_generator :
    endomorphism domain.G = generatorMultiple eigenvalue := by decide +kernel

def signedBase (r : Int) (p : Curve.Point) : Curve.Point :=
  if r < 0 then Curve.neg domain p else p

def generatorWindow (k : Nat) : Curve.Point :=
  let r := centered (splitFirst k)
  let s := centered (splitSecond k)
  signedWindow (signedBase r domain.G) (signedBase s (endomorphism domain.G)) 32 r.natAbs s.natAbs

private theorem signedBase_multiple (r k : Int) :
    signedBase r (generatorMultiple k) = generatorMultiple (if r < 0 then -k else k) := by
  unfold signedBase
  split <;> simp only [generatorMultiple_neg]

private theorem natAbs_mul_signed (r k : Int) :
    (r.natAbs : Int) * (if r < 0 then -k else k) = r * k := by
  cases r with
  | ofNat n =>
    rw [ite_eq_right (show ¬ Int.ofNat n < 0 from Int.not_lt.mpr (Int.natCast_nonneg n))]
    rfl
  | negSucc n =>
    rw [ite_eq_left (Int.negSucc_lt_zero _), Int.mul_neg, ← Int.neg_mul]
    rfl

theorem generatorWindow_eq_scalarMul (k : Nat) (hk : k < domain.n) :
    generatorWindow k = Curve.scalarMul domain k domain.G := by
  have hG : domain.G = generatorMultiple 1 := by decide +kernel
  dsimp only [generatorWindow]
  have hbase := congrArg (signedBase (centered (splitFirst k))) hG
  rw [endomorphism_generator, hbase, signedBase_multiple, signedBase_multiple,
    signedWindow_multiple, natAbs_mul_signed, natAbs_mul_signed, Int.mul_one]
  unfold generatorMultiple
  rw [(split_correct k hk).1, Int.toNat_natCast]

theorem generatorWindow_ne_infinity (k : Nat) (hpos : 0 < k) (hlt : k < domain.n) :
    generatorWindow k ≠ .infinity := by
  rw [generatorWindow_eq_scalarMul k hlt]
  intro hz
  have hk : generatorMultiple k = .infinity := by
    simpa only [generatorMultiple, Int.ofNat_mod_ofNat, Int.toNat_natCast, Nat.mod_eq_of_lt hlt] using hz
  have hzero (i : Nat) : generatorMultiple ((k * i : Nat) : Int) = .infinity := by
    induction i with
    | zero =>
      simp only [Nat.mul_zero, Int.natCast_zero]
      decide +kernel
    | succ i ih =>
      rw [Nat.mul_succ, Int.natCast_add, ← generatorMultiple_add, ih, hk]
      rfl
  have hpow := K256.Proofs.Common.Arithmetic.CubicNonzero.pow_pred_prime_mod domain.n k order_prime
    (order_prime.coprime_of_lt hpos hlt)
  have hexp : domain.n - 1 = domain.n - 2 + 1 := by decide +kernel
  rw [hexp, Nat.pow_succ, Nat.mul_comm] at hpow
  have hbad := hzero (k ^ (domain.n - 2))
  simp only [generatorMultiple, Int.ofNat_mod_ofNat, Int.toNat_natCast, hpow] at hbad
  exact (by decide +kernel : Curve.scalarMul domain 1 domain.G ≠ .infinity) hbad

theorem publicKey_eq_generatorWindow (input : ByteArray) (k : Nat)
    (h : Keys.decodeSecret domain input = some k) :
    Keys.publicKey domain input = some (generatorWindow k) := by
  have hk : k < domain.n := by
    dsimp only [Keys.decodeSecret] at h
    split at h <;> simp_all
  simp [Keys.publicKey, h, generatorWindow_eq_scalarMul k hk]

end K256.Proofs.Generate.Curve
