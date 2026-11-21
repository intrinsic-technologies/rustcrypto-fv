import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Zero

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd

theorem correction_sign (p : Inputs) (s : LoopState) (hf : Valid s.f) (hd : Valid s.d) :
    Correction.signBit (correctionInput p s) =
      LinearCombination.signByte (negative s.f != negative s.d) := by
  unfold Correction.signBit correctionInput
  rw [hf, hd]
  change (((LinearCombination.signByte (negative s.f)).setWidth 64).setWidth 8 ^^^
    LinearCombination.signByte (negative s.d)) &&& 1 = _
  cases negative s.f <;> cases negative s.d <;> decide +kernel

theorem correction_value (p : Inputs) (s : LoopState) (hf : Valid s.f) (hd : Valid s.d)
    (hb : magnitude s.d < modulus p) :
    packFour ((Correction.correctedWords (correctionInput p s)).map BitVec.toNat) =
      ((if negative s.f then -value s.d else value s.d) % (modulus p : Int)).toNat := by
  have hb' : (Correction.limbs (correctionInput p s).magnitude).toNat <
      (Correction.limbs (correctionInput p s).modulus).toNat := by
    rw [← Support.packed_limbs, ← Support.packed_limbs]
    exact hb
  rw [Support.correctedWords_signed _ hb', correction_sign p s hf hd]
  rw [← Support.packed_limbs, ← Support.packed_limbs]
  change ((if LinearCombination.signByte (negative s.f != negative s.d) = 0 then
      (magnitude s.d : Int) else -(magnitude s.d : Int)) % (modulus p : Int)).toNat = _
  unfold value LinearCombination.inputValue
  change _ = ((if negative s.f then
    -(if negative s.d then -(magnitude s.d : Int) else (magnitude s.d : Int))
    else (if negative s.d then -(magnitude s.d : Int) else (magnitude s.d : Int))) %
      (modulus p : Int)).toNat
  cases negative s.f <;> cases negative s.d <;> simp [LinearCombination.signByte]

theorem negative_iff_lt (w : SignedWords) (h : 0 < magnitude w) :
    negative w = true ↔ value w < 0 := by
  unfold value LinearCombination.inputValue
  change negative w = true ↔ (if negative w then -(magnitude w : Int) else (magnitude w : Int)) < 0
  cases negative w <;> simp <;> omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
