import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Batch.Arithmetic
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Correct
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Correct

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd

def magnitude (w : SignedWords) : Nat := packFour (w.words.map BitVec.toNat)

def negative (w : SignedWords) : Bool := w.sign == 1

def value (w : SignedWords) : Int := LinearCombination.inputValue w.words (negative w)

def Valid (w : SignedWords) : Prop := w.sign = LinearCombination.signByte (negative w)

def state (s : LoopState) : DivState := ⟨s.delta.toInt, value s.f, value s.g⟩

theorem valid_sign (w : Vector (BitVec 64) 4) (b : Bool) :
    Valid ⟨w, LinearCombination.signByte b⟩ := by cases b <;> rfl

theorem value_sign (w : Vector (BitVec 64) 4) (b : Bool) :
    value ⟨w, LinearCombination.signByte b⟩ = LinearCombination.inputValue w b := by
  cases b <;> rfl

theorem value_natAbs (w : SignedWords) : (value w).natAbs = magnitude w := by
  unfold value LinearCombination.inputValue magnitude
  cases negative w <;> simp

theorem packed_mod_low (w : Vector (BitVec 64) 4) :
    packFour (w.map BitVec.toNat) % 2^63 = w[0].toNat % 2^63 := by
  simp only [packFour, Vector.getElem_map, P256.Proofs.Field.Montgomery.wordBase]
  omega

theorem low_mask (w : BitVec 64) : (w &&& 0x7fffffffffffffff).toNat = w.toNat % 2^63 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 63

theorem signed_mask (w : BitVec 64) (b : Bool) :
    ((-(LinearCombination.signByte b).setWidth 64) &&& ((-w) ^^^ w)) ^^^ w =
      if b then -w else w := by
  cases b
  · simp [LinearCombination.signByte]
  · change (BitVec.allOnes 64 &&& ((-w) ^^^ w)) ^^^ w = -w
    simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem lowWord_signed (w : SignedWords) (h : Valid w) :
    (lowWord w).toInt = Machine.signedLow (magnitude w) (negative w) := by
  have hm := low_mask w.words[0]
  have hb : (w.words[0] &&& 0x7fffffffffffffff).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hm]
    have hlt := Nat.mod_lt w.words[0].toNat (by decide : 0 < 2^63)
    omega
  have hi := BitVec.toInt_eq_toNat_of_msb hb
  rw [hm] at hi
  have hn := BitVec.toInt_neg_eq_of_msb hb
  unfold lowWord
  rw [h, signed_mask]
  cases he : negative w
  · simpa only [Machine.signedLow, Bool.false_eq_true, ite_false, magnitude, packed_mod_low]
      using hi
  · simpa only [Machine.signedLow, ite_true, magnitude, packed_mod_low, hi] using hn

theorem batch_low (s : LoopState) (hf : Valid s.f) (hg : Valid s.g) :
    Machine.LowBitsEq 63 (Batch.state (batchInput s)) (state s) := by
  refine ⟨rfl, ?_, ?_⟩
  · change (2 : Int)^63 ∣ (lowWord s.f).toInt - value s.f
    rw [lowWord_signed s.f hf]
    exact Machine.signedLow_congruent _ _
  · change (2 : Int)^63 ∣ (lowWord s.g).toInt - value s.g
    rw [lowWord_signed s.g hg]
    exact Machine.signedLow_congruent _ _

theorem batch_matrix_identity (s : LoopState) :
    Batch.matrix (batchInput s) = Matrix.identity := rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
