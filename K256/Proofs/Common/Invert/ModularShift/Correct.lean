import K256.Proofs.Common.Invert.ModularShift.Final

namespace K256.Proofs.Common.Invert.ModularShift.Arithmetic

open X86Proofs
open LinearCombination (Limbs)

def resultNegative (p : Inputs) (negative : Bool) := negative != decide (v108b25 p ≠ 0)

theorem result_correct (p : Inputs) (negative : Bool) (x : Int)
    (sign : p.sign = if negative then 1 else 0)
    (input : x = if negative then -(wideValue (wideLow p) (wideHigh p) : Int)
      else (wideValue (wideLow p) (wideHigh p) : Int))
    (hi : p.shift.toNat ≤ 62) (bound : x.natAbs < 2^p.shift.toNat * prime.toNat) :
    let y := if resultNegative p negative then -((limbs (resultWords p)).toNat : Int)
      else ((limbs (resultWords p)).toNat : Int)
    resultSign p = (if resultNegative p negative then 1 else 0) ∧ y.natAbs < prime.toNat ∧
      ((2 : Int)^p.shift.toNat * y) % prime.toNat = x % prime.toNat := by
  have mag : x.natAbs = wideValue (wideLow p) (wideHigh p) := by
    rw [input]
    cases negative <;> simp
  have q := quotient_value p hi (mag ▸ bound)
  have h := signed_quotient_result hi input q.2.2 bound
  refine ⟨?_, ?_⟩
  · simp only [resultSign, v108d40, setWidth_mergeGPR8, sign, resultNegative]
    cases negative <;> by_cases h : v108b25 p = 0#64 <;> simp [h]
  · rw [resultWords_eq p q.1 q.2.1]
    exact h

end K256.Proofs.Common.Invert.ModularShift.Arithmetic
