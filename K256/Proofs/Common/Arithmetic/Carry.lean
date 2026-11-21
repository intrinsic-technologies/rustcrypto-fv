import K256.Proofs.Common.Invert.LinearCombination.Wide
import X86Proofs.Instructions.Adc.Operation

namespace K256.Proofs.Common.Arithmetic.Carry

open X86Proofs

def value (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => value w n + 2^(64*n) * w n

theorem addChain {n : Nat} {a b r c : Nat → Nat}
    (row : ∀ i < n, r i + 2^64 * c (i+1) = a i + b i + c i) :
    value r n + 2^(64*n) * c n = value a n + value b n + c 0 := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have low := ih fun i hi => row i (Nat.lt_succ_of_lt hi)
    have high := congrArg (fun x => 2^(64*n) * x) (row n (Nat.lt_succ_self n))
    simp only [Nat.mul_add, ← Nat.mul_assoc] at high
    simp only [value, Nat.mul_succ 64 n, Nat.pow_add]
    omega

theorem subChain {n : Nat} {a b r c : Nat → Nat}
    (row : ∀ i < n, r i + b i + c i = a i + 2^64 * c (i+1)) :
    value r n + value b n + c 0 = value a n + 2^(64*n) * c n :=
  (addChain fun i hi => (row i hi).symm).symm

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (adcSpec c a b).1.toNat + 2^64*(adcSpec c a b).2.CF.toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  simp only [adcSpec, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  by_cases h : (a.toNat+b.toNat+c.toNat)%2^64 = a.toNat+b.toNat+c.toNat <;>
    simp only [h, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
      Bool.toNat_true, Bool.toNat_false] <;> omega

theorem add_carry (a b : BitVec 64) :
    (addSpec a b).1.toNat + 2^64*(addSpec a b).2.CF.toNat = a.toNat + b.toNat := by
  simpa [adcSpec, addSpec] using adc_carry a b false

export Invert.LinearCombination (sub_borrow sbb_borrow subWord_borrow)

theorem maskedSelect {w : Nat} (a b : BitVec w) (c : Bool) :
    (-(if c then 1 else 0 : BitVec w) &&& (a ^^^ b)) ^^^ b = if c then a else b := by
  cases c
  · simp
  · change (-(1#w) &&& (a ^^^ b)) ^^^ b = a
    rw [BitVec.neg_one_eq_allOnes, BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end K256.Proofs.Common.Arithmetic.Carry
