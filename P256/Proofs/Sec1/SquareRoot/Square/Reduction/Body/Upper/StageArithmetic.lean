import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Field.Montgomery
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem third_value [Bindings] {s t : RamState} {v : Nat} (state : Second s t v) :
    let a : Limbs := ⟨t.regValue .r13, t.regValue .rbp, t.regValue .rbx, t.regValue .r14⟩
    let r := thirdWords a (t.regValue .r9) ((carryByte s t).setWidth 64)
    r.1.toNat + 2^256*r.2.toNat + 2^192*(v / 2^384) =
      reduceStep (reduceStep (reduceStep v)) := by
  dsimp only
  let a : Limbs := ⟨t.regValue .r13, t.regValue .rbp, t.regValue .rbx, t.regValue .r14⟩
  have h := thirdWords_value a (t.regValue .r9) ((carryByte s t).setWidth 64)
  have he : reduceStep (reduceStep v) =
      (a.toNat + 2^192*(t.regValue .r9).toNat + 2^256*((carryByte s t).setWidth 64).toNat) +
        wordBase*(2^192*(v / 2^384)) := by
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    have hs := state.value
    dsimp only [a, Limbs.toNat, wordBase] at *
    omega
  rw [he, reduceStep_add_wordMultiple, ← h]

set_option exponentiation.threshold 512 in
theorem fourth_value [Bindings] {s t : RamState} {v : Nat} (state : Third s t v)
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    let a : Limbs := ⟨t.regValue .r12, t.regValue .r15, t.regValue .r13, t.regValue .r9⟩
    let r := fourthWords a (BitVec.ofNat 64 (v / 2^384)) ((carryByte s t).setWidth 64)
      (BitVec.ofNat 64 (v / 2^448))
    r.1.toNat + 2^256*r.2.toNat = reduceFour v := by
  dsimp only
  let a : Limbs := ⟨t.regValue .r12, t.regValue .r15, t.regValue .r13, t.regValue .r9⟩
  have h := fourthWords_value a (BitVec.ofNat 64 (v / 2^384))
    ((carryByte s t).setWidth 64) (BitVec.ofNat 64 (v / 2^448))
  have hv : v < 2^512 := by
    exact Nat.lt_trans bound (by
      simpa only [← Nat.pow_add] using
        Nat.mul_lt_mul_of_pos_right p_lt_radix (Nat.pow_pos (by decide) (n := 256)))
  have split : v / 2^384 = (BitVec.ofNat 64 (v / 2^384)).toNat +
      wordBase*(BitVec.ofNat 64 (v / 2^448)).toNat := by
    simp only [BitVec.toNat_ofNat, wordBase]
    have hd : (v / 2^384) / 2^64 = v / 2^448 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    omega
  have he : reduceStep (reduceStep (reduceStep v)) =
      (a.toNat + 2^192*(BitVec.ofNat 64 (v / 2^384)).toNat +
        2^256*((carryByte s t).setWidth 64).toNat) +
          wordBase*(2^192*(BitVec.ofNat 64 (v / 2^448)).toNat) := by
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    have hs := state.value
    rw [split] at hs
    dsimp only [a, Limbs.toNat, wordBase] at *
    omega
  change _ = reduceStep (reduceStep (reduceStep (reduceStep v)))
  rw [he, reduceStep_add_wordMultiple]
  exact h

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
