import P256.Proofs.Scalar.Inverse.Convergence
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic

namespace P256.Proofs.Scalar.Inverse

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
open P256.Proofs.Field.Inverse.SafeGcd

theorem final_unit (p : Core.Inputs) (hc : Conditions p)
    (hn : modulus p = P256.Spec.Operations.domain.n) (ha : 0 < argument p) :
    magnitude (finalState p).f = 1 := by
  have h := final_invariant p hc
  have hb : argument p < P256.Spec.Operations.domain.n := hn ▸ hc.argument_lt
  have hs : state (finalState p) =
      divsteps 591 ⟨1, P256.Spec.Operations.domain.n, argument p⟩ := by
    simpa only [initialDivState, hn] using h.state_eq
  have hu := divsteps_591_unit ha hb
  rw [← hs] at hu
  simpa only [state, value_natAbs] using hu

theorem result_product (p : Core.Inputs) (hc : Conditions p)
    (hn : modulus p = P256.Spec.Operations.domain.n) (ha : 0 < argument p) :
    packFour ((resultWords p).map BitVec.toNat) < modulus p ∧
      packFour ((resultWords p).map BitVec.toNat) * argument p % modulus p = scale p := by
  have h := final_invariant p hc
  have hf := final_unit p hc hn ha
  have hf' : (value (finalState p).f).natAbs = 1 := by rwa [value_natAbs]
  have ht := Shared.Coefficients.coefficient_terminal hc.positive hc.scale_lt hf' h.dRelation
  have hv := correction_value p (finalState p) h.fValid h.dValid h.dBound
  have hnegative := negative_iff_lt (finalState p).f (by omega)
  have hif : (if negative (finalState p).f then -value (finalState p).d
      else value (finalState p).d) =
      (if value (finalState p).f < 0 then -value (finalState p).d else value (finalState p).d) := by
    simp only [hnegative]
  rw [hif] at hv
  change packFour ((resultWords p).map BitVec.toNat) = _ at hv
  rw [hv]
  exact ht

theorem resultChoice_one (p : Core.Inputs) (hc : Conditions p)
    (hn : modulus p = P256.Spec.Operations.domain.n) (ha : 0 < argument p) :
    resultChoice p = 1 := by
  have hf := final_unit p hc hn ha
  have hw : (finalState p).f.words = #v[1, 0, 0, 0] := by
    have hvalue := hf
    simp only [magnitude, packFour, Vector.getElem_map, Field.Montgomery.wordBase] at hvalue
    have h0 : (finalState p).f.words[0] = 1 :=
      BitVec.eq_of_toNat_eq (by change _ = 1; omega)
    have h1 : (finalState p).f.words[1] = 0 :=
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)
    have h2 : (finalState p).f.words[2] = 0 :=
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)
    have h3 : (finalState p).f.words[3] = 0 :=
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)
    apply Vector.ext
    intro i hi
    have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases idx with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hz : zeroWords p.a = false := by
    cases he : zeroWords p.a
    · rfl
    · have hz := (zeroWords_iff p.a).mp he
      change argument p = 0 at hz
      omega
  unfold resultChoice
  rw [hz, hw]
  decide +kernel

end P256.Proofs.Scalar.Inverse
