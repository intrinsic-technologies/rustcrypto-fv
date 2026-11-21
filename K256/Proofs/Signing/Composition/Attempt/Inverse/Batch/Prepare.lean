import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Prepare
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core (base roundsBefore)
open Generate.Generator.Affine.Invert.Core.Batch (count Inner Controls setupWrites
  initialWords lowWord_congruent deltaBound work)
open Verify.Core (Registers)
open Standards.SECG.DomainParameters.Secp256k1

open Generate.LIR

open_order_batch Prepare (loadInputs initializeRows)

private theorem initialWords_low {entry b : Registers} {m p : Ram} {sp : Word} {z : Nat}
    {n : Nat} {d e : Int} (state : LoopState entry m sp z n b p d e) (hn : n ≤ 591) :
    SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state (initialWords b p sp)) (Verify.Core.Scalars.Inverse.model z n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (b[5].get 64).toInt = _
    rw [state.delta]
    change (BitVec.ofInt 64 (Verify.Core.Scalars.Inverse.model z n).delta).toInt = _
    have h := deltaBound n ⟨1, domain.n, z⟩
    change (Verify.Core.Scalars.Inverse.model z n).delta.natAbs ≤ 1 + 2 * n at h
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (120 : Word) + 32 = 152 from by decide +kernel] using
      lowWord_congruent state.fValue
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (168 : Word) + 32 = 200 from by decide +kernel] using
      lowWord_congruent state.gValue

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Nat}

theorem prepare (h : Entry a m sp z) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) :
    ∃ c q s, Reaches .l1091e4 b p .l1092a0 c q ∧ Controls b c ∧
      RamWriteFrame p q (setupWrites sp) ∧ Inner c q sp s (count j) ∧
      memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j) ∧
      memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j) ∧
      SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state s) (Verify.Core.Scalars.Inverse.model z (roundsBefore j)) ∧
      SafeGcd.Batch.matrix s = SafeGcd.Matrix.identity := by
  have lo := h.depthBound
  have hi := h.high
  have window : Writable Extracted.programImage p (base sp) 360 :=
    (h.stack.of_frame state.frame).sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  obtain ⟨c, q, head, rsp, delta, f, signF, g, counter, kept, frame, signG, shift, remaining⟩ :=
    loadInputs hj state.rsp state.remaining window
  have delta' : c[5] = ⟨64, (initialWords b p sp).delta⟩ := by
    rw [delta]
    change b[5] = ⟨64, b[5].get 64⟩
    rw [state.delta]
    simp only [Value.get, BitVec.setWidth_eq]
  obtain ⟨out, tail, kept', inner⟩ :=
    initializeRows (window.of_frame frame) rsp delta' f signF g signG counter
  refine ⟨out, _, initialWords b p sp, ?_, fun i hi => (kept' i hi).trans (kept i hi),
    ?_, inner, ?_, ?_, initialWords_low state (Nat.min_le_right _ _), rfl⟩
  · refine .step (b := ⟨⟨.l109246, c, q⟩, []⟩) ?_ (.step ?_ (.refl _))
    · change program.step _ _ = _
      simp only [Program.step, head, Transfer.next]
    · change program.step _ _ = _
      simp only [Program.step, tail, Transfer.next]
  · simp only [setupWrites, work, List.singleton_append] at frame ⊢
    have bounds := window.readable.low
    slot_state region
  · segment_words [shift]
  · segment_words [remaining]

end K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
