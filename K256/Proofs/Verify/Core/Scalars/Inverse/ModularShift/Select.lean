import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.State
import K256.Proofs.Common.Invert.LinearCombination.Core

namespace K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open K256.Proofs.Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)
open Correction K256.Proofs.Common.Tactic

private theorem restoreWord (v : Value) (width : v.width = 64) :
    (⟨64, v.get 64⟩ : Value) = v := by
  rcases v with ⟨w, x⟩
  change w = 64 at width
  subst w
  rfl

private theorem maskShiftCount (w : BitVec 32) (bound : w.toNat < 64) :
    shiftCount 64 (w.setWidth 8) = w.toNat := by
  simp only [shiftCount, ite_true, BitVec.toNat_setWidth]
  omega

private theorem resultAt {m : Ram} {dst : Word} {p : Inputs}
    (h : memLoad m dst 64 = v108d90 p ∧ memLoad m (dst + 8) 64 = v108da5 p ∧
      memLoad m (dst + 16) 64 = v108dba p ∧ memLoad m (dst + 24) 64 = v108dcf p ∧
      memLoad m (dst + 32) 8 = resultSign p) :
    WordsAt m dst 64 (resultWords p) ∧ memLoad m (dst + 32) 8 = resultSign p := by
  refine ⟨?_, h.2.2.2.2⟩
  intro i hi
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases indices with rfl | rfl | rfl | rfl
  · change memLoad m (dst + 0) 64 = v108d90 p
    rw [show (dst + 0 : Word) = dst by bv_omega]
    exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem select {a b : Registers} {m m' : Ram} {sp dst ret : Word} {p : Inputs}
    (fr : CalleeFrame a m sp dst ret 304 33)
    (tf : TailFrame a m sp dst ret b m')
    (stackArgs : Readable m (sp + 8) 16)
    (argHigh : sp.toNat + 24 ≤ 2^32)
    (argApart : dst.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 24 ≤ dst.toNat)
    (pos : 0 < p.shift.toNat) (bound : p.shift.toNat ≤ 62)
    (atoms : Atom.All Extracted.programImage b m' (beforeSelect sp dst p)) :
    ∃ out, CalleeExec .l108bc1 b m' out ∧ CalleeResult a m sp dst ret 304 33 out ∧
      WordsAt out.store dst 64 (resultWords p) ∧ memLoad out.store (dst + 32) 8 = resultSign p := by
  have low := fr.depthBound
  have high := argHigh
  have apart := fr.apart
  have stackLow : (sp - 304 : Word).toNat = sp.toNat - 304 :=
    BitVec.toNat_sub_of_le (by exact low)
  have destHigh := fr.output.readable.low
  have stack : Writable Extracted.programImage m' (sp - 304) 304 := fr.stack.of_frame tf.frame
  have dest := fr.output.of_frame tf.frame
  have retRead := fr.returnSlot.of_frame tf.frame
  have retVal := tf.returned
  have saved := tf.saved
  have rsp : b[4].get 64 = sp - 168 := congrArg (Value.get 64) tf.rsp
  simp only [beforeSelect, Atom.All, Atom.Holds] at atoms
  simp only [Atom.All, Atom.Holds] at saved
  lifted_inputs atoms
  obtain ⟨save5, save15, save14, save13, save12, save3, _⟩ := saved
  have g0 := congrArg (Value.get 64) input11
  have g1 := congrArg (Value.get 64) input6
  have g2 := congrArg (Value.get 64) input13
  have g3 := congrArg (Value.get 64) input1
  have g5 := congrArg (Value.get 64) input0
  have g6 := congrArg (Value.get 64) input8
  have g7 := congrArg (Value.get 64) input7
  have g8 := congrArg (Value.get 64) input10
  have g10 := congrArg (Value.get 64) input12
  have g11 := congrArg (Value.get 64) input14
  have g12 := congrArg (Value.get 64) input2
  have g13 := congrArg (Value.get 64) input3
  have g14 := congrArg (Value.get 64) input4
  have g15 := congrArg (Value.get 64) input5
  simp only [Value.get_mk] at g0 g1 g2 g3 g5 g6 g7 g8 g10 g11 g12 g13 g14 g15
  lifted_registers [g0, g1, g2, g3, g5, g6, g7, g8, g10, g11, g12, g13, g14, g15]
  have shiftNat : (v1089a7 p).toNat = 64 - p.shift.toNat := by
    simp only [v1089a7, BitVec.reduceSetWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    exact BitVec.toNat_sub_of_le (by exact Nat.le_trans bound (by decide : 62 ≤ 64))
  have leftShift := (maskShiftCount (v1089a7 p) (by rw [shiftNat]; omega)).trans shiftNat
  have rightShift := maskShiftCount p.shift (by omega)
  let regions : List MemoryRegion := [⟨(sp - 304).toNat, 304⟩, ⟨dst.toNat, 33⟩]
  have writes : RamWriteFrame m m' regions := by
    apply (RamWriteFrame.refl m regions).trans tf.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval [b_l108bc1, b_l108bc1_1, b_l108bc1_2, b_l108bc1_3, b_l108bc1_4, b_l108bc1_5, b_l108bc1_6, b_l108bc1_7, b_l108bc1_8, rsp, g0, g1, g2, g3, g5, g6, g7, g8, g10, g11, g12, g13, g14, g15,
      input20, input21, input22, input23, input24, input25, input26, input27, input28, input29,
      leftShift, rightShift]
    segment_words [retVal, save5, save15, save14, save13, save12, save3,
      g0, g1, g2, g3, g5, g6, g7, g8, g10, g11, g12, g13, g14, g15,
      input20, input21, input22, input23, input24, input25, input26, input27, input28, input29,
      leftShift, rightShift]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_)
    all_goals try slot_guard using code_l108bc1
    all_goals try
      constructor
      · slot_guard using code_l108bc1
      · segment_words [retVal, input21]
        exact fr.retLow
    all_goals try rfl
  case post =>
    refine ⟨⟨rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
    · intro ⟨i, hi⟩ h hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact restoreWord _ hw
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact tf.controls 22 (by decide)
      · exact tf.controls 39 (by decide)
      · exact tf.controls 50 (by decide)
      · exact tf.controls 51 (by decide)
    · dsimp only [Output.store]
      change RamWriteFrame m _ regions
      dsimp only [regions] at writes ⊢
      slot_state region
    · apply resultAt
      dsimp only [Output.store]
      segment_words [resultSign, v108d40, setWidth_mergeGPR8]
      simp (disch := decide) only [BitVec.setWidth_eq, BitVec.setWidth_setWidth,
        BitVec.reduceSetWidth, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
        K256.Proofs.Common.Invert.LinearCombination.addSpec_low, setWidth_mergeGPR8,
        v108bc1, v108bc4, v108bc7, v108bca, v108bcd, v108bd0, v108bd3, v108bd6, v108bd9,
        v108bdc, v108bdf, v108be2, v108be5, v108beb, v108bee, v108bf1, v108bfa, v108bfd,
        v108c00, v108c0a, v108c12, v108c15, v108c21, v108c26, v108c2e, v108c31, v108c34,
        v108c37, v108c3c, v108c44, v108c49, v108c4e, v108c51, v108c54, v108c5f, v108c65,
        v108c6b, v108c6e, v108c71, v108c74, v108c77, v108c88, v108c95, v108c98, v108c9c,
        v108ca2, v108ca8, v108cab, v108cae, v108cb1, v108cb4, v108cbf, v108ccc, v108ccf,
        v108cd3, v108cd9, v108cdf, v108ce2, v108ce5, v108ce8, v108ceb, v108cf6, v108cfb,
        v108d06, v108d09, v108d0d, v108d13, v108d19, v108d1c, v108d1f, v108d22, v108d25,
        v108d33, v108d36, v108d4b, v108d87, v108d8a, v108d8d, v108d90, v108d9c, v108d9f,
        v108da2, v108da5, v108db1, v108db4, v108db7, v108dba, v108dc6, v108dc9, v108dcc,
        v108dcf]
      repeat' apply And.intro
      all_goals first | exact True.intro | rfl | (change Eq (_ : Word) _; lifted_word_eq [])

end K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift
