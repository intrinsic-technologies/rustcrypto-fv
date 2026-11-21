import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Arithmetic
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Prepare
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Run
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

variable {a : Registers} {m : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

theorem batch (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {b : Registers} {p : Ram} {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) :
    ∃ c q d' e', Reaches .l1091e4 b p (batchLabel (j + 1)) c q ∧
      LoopState a m sp z (roundsBefore (j + 1)) c q d' e' := by
  obtain ⟨c, q, s, prep, kept, setup, inner, shift, rem, lowBits, identity⟩ :=
    Batch.prepare h hj state
  have lo := h.low
  have hi := h.high
  obtain ⟨pos, limit, rounds⟩ := Batch.count_spec hj
  have writable := (h.stack.of_frame state.frame).of_frame setup
  obtain ⟨c', q', run, kept', frame, rows⟩ := Batch.runWords pos limit inner lo hi
    (writable.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  have modelNext : SafeGcd.divsteps (Batch.count j) (Core.model z (roundsBefore j)) =
      Core.model z (roundsBefore (j+1)) := by
    rw [Core.model, ← SafeGcd.divsteps_add, rounds, Core.model]
  have delta : s.delta.toInt.natAbs + 2 * Batch.count j ≤ 1183 := by
    have hv := lowBits.1
    change s.delta.toInt = (Core.model z (roundsBefore j)).delta at hv
    rw [hv]
    have hd := Batch.deltaBound (roundsBefore j) ⟨1, modulus, z.val⟩
    change (Core.model z (roundsBefore j)).delta.natAbs ≤ 1 + 2 * roundsBefore j at hd
    have hn : roundsBefore (j+1) ≤ 591 := Nat.min_le_right _ _
    omega
  have odd : (Core.model z (roundsBefore j)).f % 2 = 1 :=
    SafeGcd.divsteps_odd _ (s := ⟨1, modulus, z.val⟩) (by decide +kernel : (modulus : Int) % 2 = 1)
  obtain ⟨rep, bound⟩ := SafeGcd.Batch.matrix_represents _ s _ delta limit lowBits identity odd
  have newDelta := (SafeGcd.Batch.matrix_correct _ s _ delta limit lowBits identity).2
  rw [modelNext] at rep newDelta
  have shiftEq : memLoad q' (base sp + 116) 32 = memLoad q (base sp + 116) 32 := by
    apply frame.memLoad_eq
    simp only [Batch.work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  have remEq : memLoad q' (base sp + 352) 64 = memLoad q (base sp + 352) 64 := by
    apply frame.memLoad_eq
    simp only [Batch.work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  have ⟨last, mem, d', e', tail, post⟩ := Batch.update h hj state rows
    (fun i hi => (kept' i hi).trans (kept i hi))
    (setup.trans frame (fun r hr => ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩))
    (shiftEq.trans shift) (remEq.trans rem)
    newDelta rep bound
  exact ⟨last, mem, d', e', (prep.trans run).trans tail, post⟩

end K256.Proofs.Generate.Generator.Affine.Invert.Core
