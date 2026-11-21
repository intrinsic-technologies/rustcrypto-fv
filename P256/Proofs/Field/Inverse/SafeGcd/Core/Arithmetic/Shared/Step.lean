import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Bounds
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Basic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd

theorem linear_step (a b : SignedWords) (u v : BitVec 64) (count : Nat) (z : Int)
    (ha : Valid a) (hb : Valid b) (hc : count ≤ 62) (hz : z.natAbs < 2^256)
    (he : value a * u.toInt + value b * v.toInt = (2 : Int)^count * z) :
    let p : LinearShift.Inputs := ⟨linearInput a b u v, BitVec.ofNat 32 count⟩
    Valid ⟨LinearShift.shiftedWords p, LinearShift.resultSign p⟩ ∧
      value ⟨LinearShift.shiftedWords p, LinearShift.resultSign p⟩ = z := by
  intro p
  have hs : p.shift.toNat = count := by
    change count % 2^32 = count
    exact Nat.mod_eq_of_lt (by omega)
  have hsign := LinearCombination.resultSign_correct p.linear (negative a) (negative b) ha hb
  change LinearShift.resultSign p = _ at hsign
  have he' : LinearCombination.inputValue p.linear.a (negative a) * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b (negative b) * p.linear.v.toInt =
      (2 : Int)^count * z := he
  have hq : (LinearCombination.inputValue p.linear.a (negative a) * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b (negative b) * p.linear.v.toInt).natAbs /
      2^p.shift.toNat < 2^256 := by
    rw [he', hs, Int.natAbs_mul, Int.natAbs_pow]
    change 2^count * z.natAbs / 2^count < 2^256
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos count)]
    exact hz
  have hd : (2 : Int)^p.shift.toNat ∣
      LinearCombination.inputValue p.linear.a (negative a) * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b (negative b) * p.linear.v.toInt := by
    rw [he', hs]
    exact Int.dvd_mul_right _ _
  have h := LinearShift.shiftedWords_signed p (negative a) (negative b) ha hb
    (by omega) hq hd
  rw [he', hs, Int.mul_ediv_cancel_left _ (Int.ne_of_gt (Int.pow_pos (by decide)))] at h
  rw [hsign]
  exact ⟨valid_sign _ _, (value_sign _ _).trans h⟩

theorem modular_step (p : Inputs) (a b : SignedWords) (u v : BitVec 64) (count : Nat)
    (ha : Valid a) (hb : Valid b) (hc : count ≤ 62)
    (hm : 0 < packFour (p.modulus.map BitVec.toNat))
    (hi : ((packFour (p.modulus.map BitVec.toNat) : Int) * p.inverse.toNat) %
      (2 : Int)^64 = 1)
    (hbound : (value a * u.toInt + value b * v.toInt).natAbs <
      2^count * packFour (p.modulus.map BitVec.toNat)) :
    let q : ModularShift.Inputs :=
      ⟨linearInput a b u v, BitVec.ofNat 32 count, p.modulus, p.inverse, 0⟩
    let w : SignedWords := ⟨ModularShift.resultWords q, ModularShift.resultSign q⟩
    Valid w ∧ magnitude w < packFour (p.modulus.map BitVec.toNat) ∧
      ((2 : Int)^count * value w) % packFour (p.modulus.map BitVec.toNat) =
      (value a * u.toInt + value b * v.toInt) % packFour (p.modulus.map BitVec.toNat) := by
  intro q w
  have hs : q.shift.toNat = count := by
    change count % 2^32 = count
    exact Nat.mod_eq_of_lt (by omega)
  have h := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic.correct q (negative a) (negative b) ha hb
    (by omega) hm hi (by simpa only [hs, q, linearInput, value] using hbound)
  have hv : value w = LinearCombination.inputValue (ModularShift.resultWords q)
      (P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic.resultNegative q (negative a) (negative b)) := by
    change value ⟨_, ModularShift.resultSign q⟩ = _
    rw [h.1, value_sign]
  refine ⟨?_, h.2.1, ?_⟩
  · change Valid ⟨_, ModularShift.resultSign q⟩
    rw [h.1]
    exact valid_sign _ _
  · rw [hv]
    simpa only [hs, q, linearInput, value] using h.2.2

theorem next_fg (p : Inputs) (s : LoopState)
    (hf : Valid s.f) (hg : Valid s.g)
    (hdelta : s.delta.toInt.natAbs + 2 * batchCount s ≤ 1183)
    (hodd : (value s.f) % 2 = 1)
    (hfb : magnitude s.f ≤ packFour (p.modulus.map BitVec.toNat))
    (hgb : magnitude s.g ≤ packFour (p.modulus.map BitVec.toNat)) :
    Valid (nextState p s).f ∧ Valid (nextState p s).g ∧
      state (nextState p s) = divsteps (batchCount s) (state s) := by
  have hc : batchCount s ≤ 62 := Nat.min_le_right _ _
  have hm := Batch.matrix_represents (batchCount s) (batchInput s) (state s) hdelta hc
    (batch_low s hf hg) (batch_matrix_identity s) hodd
  have hd := (Batch.matrix_correct (batchCount s) (batchInput s) (state s) hdelta hc
    (batch_low s hf hg) (batch_matrix_identity s)).2
  have hz := divsteps_natAbs_le (s := state s)
    (limit := packFour (p.modulus.map BitVec.toNat)) (batchCount s)
    (by simpa only [state, value_natAbs] using hfb)
    (by simpa only [state, value_natAbs] using hgb)
  have hlt := LinearCombination.packed_lt p.modulus
  have hfirst := linear_step s.f s.g (batchResult s).u (batchResult s).v (batchCount s)
    (divsteps (batchCount s) (state s)).f hf hg hc (Nat.lt_of_le_of_lt hz.1 hlt)
    (by simpa only [Batch.matrix, state, batchResult, Int.mul_comm] using hm.1.1)
  have hsecond := linear_step s.f s.g (batchResult s).q (batchResult s).r (batchCount s)
    (divsteps (batchCount s) (state s)).g hf hg hc (Nat.lt_of_le_of_lt hz.2 hlt)
    (by simpa only [Batch.matrix, state, batchResult, Int.mul_comm] using hm.1.2)
  refine ⟨hfirst.1, hsecond.1, ?_⟩
  have hfval : value (nextState p s).f = (divsteps (batchCount s) (state s)).f := hfirst.2
  have hgval : value (nextState p s).g = (divsteps (batchCount s) (state s)).g := hsecond.2
  have hdval : (nextState p s).delta.toInt = (divsteps (batchCount s) (state s)).delta := hd
  change DivState.mk _ _ _ = _
  rw [hfval, hgval, hdval]

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
