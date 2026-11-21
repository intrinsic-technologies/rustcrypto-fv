import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic

set_option autoImplicit false

open P256.Proofs.Field.Montgomery.Reduction
open P256.Proofs.SecretKeyFromBytes.Scalar

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum

def low (a b : Limbs) : BitVec 64 := adc b.l0 a.l0 false

def secondInput (a b : Limbs) : BitVec 64 := adc a.l1 0 (carry b.l0 a.l0 false)

def secondCarry (a b : Limbs) : Bool := carry a.l1 0 (carry b.l0 a.l0 false)

def thirdInput (a b : Limbs) : BitVec 64 := adc b.l2 a.l2 false

def highInput (a b : Limbs) : BitVec 64 := adc b.l3 a.l3 false

def second (a b : Limbs) : BitVec 64 := adc (secondInput a b) b.l1 false

def third (a b : Limbs) : BitVec 64 :=
  adc (thirdInput a b) (BitVec.ofNat 64 (secondCarry a b).toNat)
    (carry (secondInput a b) b.l1 false)

def thirdCarry (a b : Limbs) : Bool :=
  carry (thirdInput a b) (BitVec.ofNat 64 (secondCarry a b).toNat)
    (carry (secondInput a b) b.l1 false)

def high (a b : Limbs) : BitVec 64 :=
  adc (BitVec.ofNat 64 (carry b.l2 a.l2 false).toNat) (highInput a b) (thirdCarry a b)

def highCarry (a b : Limbs) : Bool :=
  carry (BitVec.ofNat 64 (carry b.l2 a.l2 false).toNat) (highInput a b) (thirdCarry a b)

def extendedCarry (a b : Limbs) : BitVec 64 :=
  adc (BitVec.ofNat 64 (carry b.l3 a.l3 false).toNat) 0 (highCarry a b)

def value (a b : Limbs) : Limbs := ⟨low a b, second a b, third a b, high a b⟩

theorem bool_word_toNat (b : Bool) : (BitVec.ofNat 64 b.toNat).toNat = b.toNat := by
  cases b <;> decide

theorem adc_bool_toNat (b c : Bool) :
    (adc (BitVec.ofNat 64 b.toNat) 0 c).toNat = b.toNat + c.toNat := by
  cases b <;> cases c <;> decide

theorem carry_chain {a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 s1 s2 s3 c0 c1 c2 c3 d1 d2 d3 e : Nat}
    (h0 : r0 + 2^64*c0 = b0+a0) (h1 : s1 + 2^64*c1 = a1+c0)
    (h2 : s2 + 2^64*c2 = b2+a2) (h3 : s3 + 2^64*c3 = b3+a3)
    (h4 : r1 + 2^64*d1 = s1+b1) (h5 : r2 + 2^64*d2 = s2+c1+d1)
    (h6 : r3 + 2^64*d3 = c2+s3+d2) (h7 : e = c3+d3) :
    r0 + 2^64*(r1 + 2^64*(r2 + 2^64*r3)) + 2^256*e =
      a0 + 2^64*(a1 + 2^64*(a2 + 2^64*a3)) +
      (b0 + 2^64*(b1 + 2^64*(b2 + 2^64*b3))) := by
  omega

theorem value_toNat (a b : Limbs) :
    (value a b).toNat + 2^256 * (extendedCarry a b).toNat = a.toNat + b.toNat := by
  have h0 := P256.Proofs.Field.Montgomery.Reduction.adc_carry b.l0 a.l0 false
  have h1 := P256.Proofs.Field.Montgomery.Reduction.adc_carry a.l1 0 (carry b.l0 a.l0 false)
  have h2 := P256.Proofs.Field.Montgomery.Reduction.adc_carry b.l2 a.l2 false
  have h3 := P256.Proofs.Field.Montgomery.Reduction.adc_carry b.l3 a.l3 false
  have h4 := P256.Proofs.Field.Montgomery.Reduction.adc_carry (secondInput a b) b.l1 false
  have h5 := P256.Proofs.Field.Montgomery.Reduction.adc_carry (thirdInput a b) (BitVec.ofNat 64 (secondCarry a b).toNat)
    (carry (secondInput a b) b.l1 false)
  have h6 := P256.Proofs.Field.Montgomery.Reduction.adc_carry (BitVec.ofNat 64 (carry b.l2 a.l2 false).toNat)
    (highInput a b) (thirdCarry a b)
  have h7 : (extendedCarry a b).toNat = (carry b.l3 a.l3 false).toNat +
      (highCarry a b).toNat := adc_bool_toNat _ _
  simp only [Bool.toNat_false, Nat.add_zero] at h0 h1 h2 h3 h4
  simp only [bool_word_toNat] at h5 h6
  change (low a b).toNat + 2^64 * (carry b.l0 a.l0 false).toNat = _ at h0
  change (secondInput a b).toNat + 2^64 * (secondCarry a b).toNat = _ at h1
  change (thirdInput a b).toNat + 2^64 * (carry b.l2 a.l2 false).toNat = _ at h2
  change (highInput a b).toNat + 2^64 * (carry b.l3 a.l3 false).toNat = _ at h3
  change (second a b).toNat + 2^64 * (carry (secondInput a b) b.l1 false).toNat = _ at h4
  change (third a b).toNat + 2^64 * (thirdCarry a b).toNat = _ at h5
  change (high a b).toNat + 2^64 * (highCarry a b).toNat = _ at h6
  simp only [value, Limbs.toNat]
  exact carry_chain h0 h1 h2 h3 h4 h5 h6 h7

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum
