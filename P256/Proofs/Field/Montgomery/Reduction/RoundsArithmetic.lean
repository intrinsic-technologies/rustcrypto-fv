import P256.Proofs.Field.Montgomery.Reduction.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

attribute [local irreducible] firstRound shiftRound

def rounds (low high : Limbs) : Limbs × (BitVec 64 × Bool) :=
  let r0 := firstRound low
  let r1 := shiftRound r0 high.l0
  let e1 := adc64 high.l1 0 r1.2
  let r2 := shiftRound r1.1 e1.1
  let e2 := adc64 (BitVec.ofNat 64 e1.2.toNat) high.l2 r2.2
  let r3 := shiftRound r2.1 e2.1
  let e3 := adc64 (BitVec.ofNat 64 e2.2.toNat) high.l3 r3.2
  (r3.1, e3)

def wideValue (a : Limbs) (extra : BitVec 64 × Bool) : Nat :=
  a.toNat + 2^192 * extra.1.toNat + 2^256 * extra.2.toNat

theorem reduceStep_add_high (a b : Nat) :
    reduceStep (a + 2^256*b) = reduceStep a + 2^192*b := by
  have he : a + 2^256*b = a + P256.Proofs.Field.Montgomery.wordBase*(2^192*b) := by
    dsimp only [P256.Proofs.Field.Montgomery.wordBase]
    omega
  rw [he, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]

set_option exponentiation.threshold 512 in
theorem rounds_value (low high : Limbs) :
    wideValue (rounds low high).1 (rounds low high).2 =
      reduceFour (low.toNat + 2^256*high.toNat) := by
  let r0 := firstRound low
  let r1 := shiftRound r0 high.l0
  let e1 := adc64 high.l1 0 r1.2
  let r2 := shiftRound r1.1 e1.1
  let e2 := adc64 (BitVec.ofNat 64 e1.2.toNat) high.l2 r2.2
  let r3 := shiftRound r2.1 e2.1
  let e3 := adc64 (BitVec.ofNat 64 e2.2.toNat) high.l3 r3.2
  change r3.1.toNat + 2^192*e3.1.toNat + 2^256*e3.2.toNat = _
  have h0 : r0.toNat = reduceStep low.toNat := firstRound_value low
  have h1 := shiftRound_value r0 high.l0
  have h2 := shiftRound_value r1.1 e1.1
  have h3 := shiftRound_value r2.1 e2.1
  have he1 := adc64_value high.l1 0 r1.2
  have he2 := adc64_value (BitVec.ofNat 64 e1.2.toNat) high.l2 r2.2
  have he3 := adc64_value (BitVec.ofNat 64 e2.2.toNat) high.l3 r3.2
  change r1.1.toNat + 2^192*r1.2.toNat = reduceStep r0.toNat + 2^128*high.l0.toNat at h1
  change r2.1.toNat + 2^192*r2.2.toNat = reduceStep r1.1.toNat + 2^128*e1.1.toNat at h2
  change r3.1.toNat + 2^192*r3.2.toNat = reduceStep r2.1.toNat + 2^128*e2.1.toNat at h3
  change e1.1.toNat + 2^64*e1.2.toNat = high.l1.toNat + 0 + r1.2.toNat at he1
  simp only [BitVec.toNat_ofNat] at he2 he3
  change e2.1.toNat + 2^64*e2.2.toNat = e1.2.toNat%2^64 + high.l2.toNat + r2.2.toNat at he2
  change e3.1.toNat + 2^64*e3.2.toNat = e2.2.toNat%2^64 + high.l3.toNat + r3.2.toNat at he3
  have he1small := Bool.toNat_le e1.2
  have he2small := Bool.toNat_le e2.2
  clear_value r0 r1 e1 r2 e2 r3 e3
  have hd : high.toNat = high.l0.toNat + 2^64*high.l1.toNat +
      2^128*high.l2.toNat + 2^192*high.l3.toNat := by
    unfold Limbs.toNat
    omega
  have stage1 : reduceStep (low.toNat + 2^256*high.toNat) =
      r0.toNat + 2^192*high.l0.toNat + 2^256*high.l1.toNat +
        2^320*high.l2.toNat + 2^384*high.l3.toNat := by
    rw [reduceStep_add_high, ← h0, hd]
    omega
  have stage2 : reduceStep (reduceStep (low.toNat + 2^256*high.toNat)) =
      r1.1.toNat + 2^192*e1.1.toNat + 2^256*(e1.2.toNat+high.l2.toNat) +
        2^320*high.l3.toNat := by
    rw [stage1]
    have he : r0.toNat + 2^192*high.l0.toNat + 2^256*high.l1.toNat +
        2^320*high.l2.toNat + 2^384*high.l3.toNat =
        r0.toNat + P256.Proofs.Field.Montgomery.wordBase *
          (2^128*high.l0.toNat + 2^192*high.l1.toNat + 2^256*high.l2.toNat +
            2^320*high.l3.toNat) := by
      dsimp only [P256.Proofs.Field.Montgomery.wordBase]
      omega
    rw [he, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
    omega
  have stage3 : reduceStep (reduceStep (reduceStep (low.toNat + 2^256*high.toNat))) =
      r2.1.toNat + 2^192*e2.1.toNat + 2^256*(e2.2.toNat+high.l3.toNat) := by
    rw [stage2]
    have he : r1.1.toNat + 2^192*e1.1.toNat + 2^256*(e1.2.toNat+high.l2.toNat) +
        2^320*high.l3.toNat = r1.1.toNat + P256.Proofs.Field.Montgomery.wordBase *
          (2^128*e1.1.toNat + 2^192*(e1.2.toNat+high.l2.toNat) + 2^256*high.l3.toNat) := by
      dsimp only [P256.Proofs.Field.Montgomery.wordBase]
      omega
    rw [he, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
    omega
  change _ = reduceStep (reduceStep (reduceStep (reduceStep (low.toNat + 2^256*high.toNat))))
  rw [stage3]
  have he : r2.1.toNat + 2^192*e2.1.toNat + 2^256*(e2.2.toNat+high.l3.toNat) =
      r2.1.toNat + P256.Proofs.Field.Montgomery.wordBase *
        (2^128*e2.1.toNat + 2^192*(e2.2.toNat+high.l3.toNat)) := by
    dsimp only [P256.Proofs.Field.Montgomery.wordBase]
    omega
  rw [he, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
  omega

theorem rounds_lt_two_mul_p (low high : Limbs)
    (h : low.toNat + 2^256*high.toNat < P256.Proofs.Field.Montgomery.p * 2^256) :
    wideValue (rounds low high).1 (rounds low high).2 < 2*P256.Proofs.Field.Montgomery.p := by
  rw [rounds_value]
  exact P256.Proofs.Field.Montgomery.reduceFour_lt_two_mul_p _ h

def normalize (a : Limbs) (extra : BitVec 64 × Bool) : Limbs × Bool :=
  let top := add64 a.l3 extra.1
  (⟨a.l0, a.l1, a.l2, top.1⟩, top.2 || extra.2)

theorem normalize_value (a : Limbs) (extra : BitVec 64 × Bool)
    (h : wideValue a extra < 2*2^256) :
    (normalize a extra).1.toNat + 2^256*(normalize a extra).2.toNat = wideValue a extra := by
  let top := add64 a.l3 extra.1
  have ht := add64_value a.l3 extra.1
  change top.1.toNat + 2^64*top.2.toNat = a.l3.toNat + extra.1.toNat at ht
  change (Limbs.mk a.l0 a.l1 a.l2 top.1).toNat + 2^256*(top.2 || extra.2).toNat = _
  clear_value top
  have hs : top.2.toNat + extra.2.toNat ≤ 1 := by
    unfold wideValue Limbs.toNat at h
    omega
  have hor : (top.2 || extra.2).toNat = top.2.toNat + extra.2.toNat := by
    cases htop : top.2 <;> cases hextra : extra.2 <;>
      simp_all only [Bool.toNat_false, Bool.toNat_true, Bool.false_or, Bool.true_or] <;> omega
  rw [hor]
  dsimp only [wideValue, Limbs.toNat]
  omega

def normalizedRounds (low high : Limbs) : Limbs × Bool :=
  normalize (rounds low high).1 (rounds low high).2

theorem normalizedRounds_value (low high : Limbs)
    (h : low.toNat + 2^256*high.toNat < P256.Proofs.Field.Montgomery.p * 2^256) :
    (normalizedRounds low high).1.toNat + 2^256*(normalizedRounds low high).2.toNat =
      reduceFour (low.toNat + 2^256*high.toNat) := by
  unfold normalizedRounds
  rw [normalize_value]
  · exact rounds_value low high
  · exact Nat.lt_trans (rounds_lt_two_mul_p low high h)
      (Nat.mul_lt_mul_of_pos_left P256.Proofs.Field.Montgomery.p_lt_radix (by decide))

theorem normalizedRounds_lt_two_mul_p (low high : Limbs)
    (h : low.toNat + 2^256*high.toNat < P256.Proofs.Field.Montgomery.p * 2^256) :
    (normalizedRounds low high).1.toNat + 2^256*(normalizedRounds low high).2.toNat <
      2*P256.Proofs.Field.Montgomery.p := by
  rw [normalizedRounds_value low high h]
  exact P256.Proofs.Field.Montgomery.reduceFour_lt_two_mul_p _ h


end P256.Proofs.Field.Montgomery.Reduction
