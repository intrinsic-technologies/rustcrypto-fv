import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.State
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.LastFold

namespace K256.Proofs.Verify.Core.Reduce

open Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply
open Common.Invert.LinearCombination (Limbs subRaw subWord subRaw_toNat shift63_toNat eq_zero_or_one)
open Common.Invert.ModularShift (limbs words limbs_toNat_lt)

open Split.Reduction (orderLimbs)

private theorem highBorrow (a b r : BitVec 64) (hb : b.msb = true) :
    Common.Invert.LinearCombination.borrow a b r = (~~~a ||| r) >>> 63 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Common.Invert.LinearCombination.borrow, shift63_toNat, BitVec.msb_or,
    BitVec.msb_and, BitVec.msb_not, hb]
  cases a.msb <;> cases r.msb <;> rfl

private theorem highSub (a v : BitVec 64) :
    subWord a orderLimbs.l3 (v >>> 63) = (((v >>> 63) - 1) >>> 63) + a := by
  have hc : v >>> 63 = 0 ∨ v >>> 63 = 1 :=
    eq_zero_or_one (by rw [shift63_toNat]; cases v.msb <;> decide)
  rcases hc with hc | hc <;> rw [hc]
  · rw [Common.Invert.LinearCombination.subWord_zero, BitVec.sub_eq_add_neg, BitVec.add_comm]
    rfl
  · change (-1#64) + (a - 0xffffffffffffffff#64) = 0#64 + a
    rw [BitVec.sub_eq_add_neg, BitVec.add_comm a, ← BitVec.add_assoc]
    rfl

private theorem difference_limbs (a : Limbs) :
    (subRaw a orderLimbs).1 =
      let s0 := 0x402da1732fc9bebf + a.l0
      let c0 := (~~~a.l0 ||| s0) >>> 63
      let s1 := 0x4551231950b75fc5 + a.l1 + (0 - c0).sshiftRight 63
      let c1 := (~~~a.l1 ||| s1) >>> 63
      let s2 := (0 - c1).sshiftRight 63 + a.l2 + 2
      let c2 := (~~~a.l2 ||| s2) >>> 63
      ⟨s0, s1, s2, ((c2 - 1) >>> 63) + a.l3⟩ := by
  have h₀ : a.l0 - orderLimbs.l0 = 0x402da1732fc9bebf + a.l0 := by
    change _ = 0x402da1732fc9bebf#64 + a.l0
    rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rfl
  have h₁ (c : BitVec 64) :
      subWord a.l1 orderLimbs.l1 c = 0x4551231950b75fc5 + a.l1 + (0 - c).sshiftRight 63 := by
    change _ = 0x4551231950b75fc5#64 + a.l1 + (0#64 - c).sshiftRight 63
    rw [subWord, BitVec.zero_sub, BitVec.sub_eq_add_neg, BitVec.add_comm a.l1, BitVec.add_comm ((-c).sshiftRight 63)]
    rfl
  have h₂ (c : BitVec 64) :
      subWord a.l2 orderLimbs.l2 c = (0 - c).sshiftRight 63 + a.l2 + 2 := by
    change _ = (0#64 - c).sshiftRight 63 + a.l2 + 2
    rw [subWord, BitVec.zero_sub, BitVec.sub_eq_add_neg, ← BitVec.add_assoc]
    rfl
  have hmsb₀ : orderLimbs.l0.msb = true := rfl
  have hmsb₁ : orderLimbs.l1.msb = true := rfl
  have hmsb₂ : orderLimbs.l2.msb = true := rfl
  dsimp only [subRaw]
  rw [h₀, highBorrow _ _ _ hmsb₀, h₁, highBorrow _ _ _ hmsb₁, h₂, highBorrow _ _ _ hmsb₂, highSub]

private theorem difference_eq (w : Vector (BitVec 64) 4) :
    difference w = words (subRaw (limbs w) orderLimbs).1 := by
  rw [difference_limbs]
  rfl

theorem reductionWords {x : Nat} (bound : x < 2^256) :
    (if x < domain.n then scalarWords x else difference (scalarWords x)) = scalarWords (x % domain.n) ∧
    borrow (scalarWords x) = (if x < domain.n then 1 else 0) := by
  let w := scalarWords x
  have value : Split.scalarValue w = x := Split.scalarWords_value x bound
  have packed : (w[3].toNat * 2^64 + w[2].toNat) * 2^128 + w[1].toNat * 2^64 + w[0].toNat = x := by
    change w[0].toNat + 2^64 * (w[1].toNat + 2^64 * (w[2].toNat + 2^64 * w[3].toNat)) = x at value
    omega
  have hborrow : borrow (scalarWords x) = (if x < domain.n then 1 else 0) := by
    change ParseSignature.Scalar.borrowChain w[0] w[1] w[2] w[3] = _
    rw [ParseSignature.Scalar.borrowChain_eq, packed]
  refine ⟨?_, hborrow⟩
  by_cases hx : x < domain.n
  · rw [ite_eq_left hx, Nat.mod_eq_of_lt hx]
  · rw [ite_eq_right hx]
    change difference w = _
    rw [difference_eq, Split.Addition.limbWords_eq]
    apply congrArg scalarWords
    let reduced := subRaw (limbs w) orderLimbs
    change reduced.1.toNat = x % domain.n
    have hdiff := (subRaw_toNat (limbs w) orderLimbs).2
    change reduced.1.toNat + domain.n = Split.scalarValue w + 2^256 * reduced.2.toNat at hdiff
    rw [value] at hdiff
    have hsmall := limbs_toNat_lt reduced.1
    have hn : 2^256 < 2 * domain.n := by decide +kernel
    have hb : reduced.2.toNat = 0 := by omega
    rw [hb, Nat.mul_zero, Nat.add_zero] at hdiff
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end K256.Proofs.Verify.Core.Reduce
