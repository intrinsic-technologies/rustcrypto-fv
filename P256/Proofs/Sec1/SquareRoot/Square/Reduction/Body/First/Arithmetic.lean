import P256.Proofs.Field.Montgomery.Reduction.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound

open P256.Proofs.Field.Montgomery
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

attribute [local irreducible] add64 adc64 product64

def lowWords (a : Limbs) : BitVec 64 × BitVec 64 :=
  let p0 := product64 0xffffffffffffffff a.l0
  let p1 := product64 0xffffffff a.l0
  let x := add64 p1.1 a.l1
  let hi1 := adc64 p1.2 0 x.2
  let z := add64 p0.1 a.l0
  let y := adc64 x.1 p0.2 z.2
  let k := adc64 hi1.1 0 y.2
  (y.1, k.1)

def words (a : Limbs) : Limbs :=
  let low := lowWords a
  let q := add64 0 a.l2
  let qh := adc64 0 0 q.2
  let w := add64 q.1 low.2
  let wh := adc64 qh.1 0 w.2
  let p3 := product64 0xffffffff00000001 a.l0
  let z3 := add64 p3.1 a.l3
  let zh := adc64 p3.2 0 z3.2
  let r3 := add64 z3.1 wh.1
  let rh := adc64 zh.1 0 r3.2
  ⟨low.1, w.1, r3.1, rh.1⟩

set_option maxHeartbeats 800000 in
theorem words_value (a : Limbs) : (words a).toNat = reduceStep a.toNat := by
  let p0 := product64 0xffffffffffffffff a.l0
  let p1 := product64 0xffffffff a.l0
  let x := add64 p1.1 a.l1
  let hi1 := adc64 p1.2 0 x.2
  let z := add64 p0.1 a.l0
  let y := adc64 x.1 p0.2 z.2
  let k := adc64 hi1.1 0 y.2
  let q := add64 0 a.l2
  let qh := adc64 0 0 q.2
  let w := add64 q.1 k.1
  let wh := adc64 qh.1 0 w.2
  let p3 := product64 0xffffffff00000001 a.l0
  let z3 := add64 p3.1 a.l3
  let zh := adc64 p3.2 0 z3.2
  let r3 := add64 z3.1 wh.1
  let rh := adc64 zh.1 0 r3.2
  have hp0 := product64_value 0xffffffffffffffff a.l0
  have hp1 := product64_value 0xffffffff a.l0
  have hx := add64_value p1.1 a.l1
  have hh := adc64_value p1.2 0 x.2
  have hz := add64_value p0.1 a.l0
  have hy := adc64_value x.1 p0.2 z.2
  have hk := adc64_value hi1.1 0 y.2
  have hq := add64_value 0 a.l2
  have hqh := adc64_value 0 0 q.2
  have hw := add64_value q.1 k.1
  have hwh := adc64_value qh.1 0 w.2
  have hp3 := product64_value 0xffffffff00000001 a.l0
  have hz3 := add64_value p3.1 a.l3
  have hzh := adc64_value p3.2 0 z3.2
  have hr3 := add64_value z3.1 wh.1
  have hrh := adc64_value zh.1 0 r3.2
  have hz0 : z.1 = 0 := by
    dsimp only [z, p0]
    unfold add64 product64
    change (0xffffffffffffffff : BitVec 64) * a.l0 + a.l0 = 0
    apply BitVec.eq_of_toNat_eq
    change ((18446744073709551615*a.l0.toNat)%2^64+a.l0.toNat)%2^64=0
    omega
  have ha := a.l0.isLt
  have hred := reduceStep_limbs_sparse a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat ha
  change reduceStep a.toNat = _ at hred
  rw [hred]
  change y.1.toNat + wordBase*(w.1.toNat + wordBase*(r3.1.toNat + wordBase*rh.1.toNat)) = _
  change p0.1.toNat + wordBase*p0.2.toNat = 18446744073709551615*a.l0.toNat at hp0
  change p1.1.toNat + wordBase*p1.2.toNat = 4294967295*a.l0.toNat at hp1
  change p3.1.toNat + wordBase*p3.2.toNat = 18446744069414584321*a.l0.toNat at hp3
  change z.1.toNat + wordBase*z.2.toNat = _ at hz
  rw [hz0] at hz
  change x.1.toNat + wordBase*x.2.toNat = p1.1.toNat + a.l1.toNat at hx
  change hi1.1.toNat + wordBase*hi1.2.toNat = p1.2.toNat + 0 + x.2.toNat at hh
  change y.1.toNat + wordBase*y.2.toNat = x.1.toNat + p0.2.toNat + z.2.toNat at hy
  change k.1.toNat + wordBase*k.2.toNat = hi1.1.toNat + 0 + y.2.toNat at hk
  change q.1.toNat + wordBase*q.2.toNat = 0 + a.l2.toNat at hq
  change qh.1.toNat + wordBase*qh.2.toNat = 0 + 0 + q.2.toNat at hqh
  change w.1.toNat + wordBase*w.2.toNat = q.1.toNat + k.1.toNat at hw
  change wh.1.toNat + wordBase*wh.2.toNat = qh.1.toNat + 0 + w.2.toNat at hwh
  change z3.1.toNat + wordBase*z3.2.toNat = p3.1.toNat + a.l3.toNat at hz3
  change zh.1.toNat + wordBase*zh.2.toNat = p3.2.toNat + 0 + z3.2.toNat at hzh
  change r3.1.toNat + wordBase*r3.2.toNat = z3.1.toNat + wh.1.toNat at hr3
  change rh.1.toNat + wordBase*rh.2.toNat = zh.1.toNat + 0 + r3.2.toNat at hrh
  clear_value p0 p1 x hi1 z y k q qh w wh p3 z3 zh r3 rh
  clear hred hz0
  dsimp only [wordBase, BitVec.toNat_ofNat] at *
  have hphi : p1.2.toNat < 2^32 := by omega
  have h3hi : p3.2.toNat < 18446744069414584321 := by omega
  have hhc : hi1.2.toNat = 0 := by have := Bool.toNat_le x.2; omega
  have hkc : k.2.toNat = 0 := by have := Bool.toNat_le x.2; have := Bool.toNat_le y.2; omega
  have hqc : q.2.toNat = 0 := by have := a.l2.isLt; omega
  have hqhc : qh.1.toNat = 0 ∧ qh.2.toNat = 0 := by omega
  have hwhc : wh.2.toNat = 0 := by have := Bool.toNat_le w.2; omega
  have hzhc : zh.2.toNat = 0 := by have := Bool.toNat_le z3.2; omega
  have hrhc : rh.2.toNat = 0 := by
    have := Bool.toNat_le z3.2
    have := Bool.toNat_le r3.2
    omega
  omega

def inputWords (v : Nat) : Limbs :=
  ⟨BitVec.ofNat 64 v, BitVec.ofNat 64 (v / 2^64),
    BitVec.ofNat 64 (v / 2^128), BitVec.ofNat 64 (v / 2^192)⟩

set_option exponentiation.threshold 512 in
theorem inputWords_value (v : Nat) :
    (words (inputWords v)).toNat + 2^192*(v / 2^256) = reduceStep v := by
  rw [words_value, reduceStep_eq, reduceStep_eq]
  simp only [inputWords, Limbs.toNat, BitVec.toNat_ofNat]
  dsimp only [wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound
