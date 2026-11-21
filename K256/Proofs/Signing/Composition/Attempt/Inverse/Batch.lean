import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.Prepare
import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.Linear
import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.Modular
import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.Copy
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Run

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Common.Field
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore batchLabel CalleeResult)
open Verify.Core (Registers)
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core.Batch (count_spec count work deltaBound runWords)

theorem batch {a : Registers} {m : Ram} {p : Word} {k : Nat} (h : Entry a m p k)
    {j : Nat} (hj : j < 10) {b : Registers} {n : Ram} {d e : Int}
    (state : LoopState a m p k (roundsBefore j) b n d e) :
    ∃ c t d' e', Reaches .l1091e4 b n (batchLabel (j+1)) c t ∧
      LoopState a m p k (roundsBefore (j+1)) c t d' e' := by
  obtain ⟨c, q, s, prep, kept, setup, inner, shift, rem, lowBits, identity⟩ :=
    Batch.prepare h hj state
  have lo := h.depthBound
  have hi := h.high
  have small : p.toNat + 129 ≤ 2^32 := by omega
  obtain ⟨pos, limit, rounds⟩ := count_spec hj
  have writable := (h.stack.of_frame state.frame).of_frame setup
  obtain ⟨c', q', run, kept', frame, rows⟩ := runWords pos limit inner lo small
    (writable.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  have modelNext : SafeGcd.divsteps (count j) (Verify.Core.Scalars.Inverse.model k (roundsBefore j)) =
      Verify.Core.Scalars.Inverse.model k (roundsBefore (j+1)) := by
    rw [Verify.Core.Scalars.Inverse.model, ← SafeGcd.divsteps_add, rounds, Verify.Core.Scalars.Inverse.model]
  have delta : s.delta.toInt.natAbs + 2 * count j ≤ 1183 := by
    have hv := lowBits.1
    change s.delta.toInt = (Verify.Core.Scalars.Inverse.model k (roundsBefore j)).delta at hv
    rw [hv]
    have hd := deltaBound (roundsBefore j) ⟨1, domain.n, k⟩
    change (Verify.Core.Scalars.Inverse.model k (roundsBefore j)).delta.natAbs ≤ 1 + 2 * roundsBefore j at hd
    have hn : roundsBefore (j+1) ≤ 591 := Nat.min_le_right _ _
    omega
  have odd : (Verify.Core.Scalars.Inverse.model k (roundsBefore j)).f % 2 = 1 :=
    SafeGcd.divsteps_odd _ (s := ⟨1, domain.n, k⟩) (by decide +kernel : (domain.n : Int) % 2 = 1)
  obtain ⟨rep, bound⟩ := SafeGcd.Batch.matrix_represents _ s _ delta limit lowBits identity odd
  have newDelta := (SafeGcd.Batch.matrix_correct _ s _ delta limit lowBits identity).2
  rw [modelNext] at rep newDelta
  have shiftEq : memLoad q' (base p + 116) 32 = memLoad q (base p + 116) 32 := by
    apply frame.memLoad_eq
    simp only [work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  have remEq : memLoad q' (base p + 352) 64 = memLoad q (base p + 352) 64 := by
    apply frame.memLoad_eq
    simp only [work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  obtain ⟨cl, ml, el, linear⟩ := Batch.linearRows h hj state rows
    (fun i hi => (kept' i hi).trans (kept i hi))
    (setup.trans frame (fun r hr => ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩))
    (shiftEq.trans shift) (remEq.trans rem) rep
  obtain ⟨cm, mm, d', e', em, modular, db, eb, dc, ec⟩ := Batch.modularRows h hj state linear bound
  obtain ⟨last, mem, tail, post⟩ := Batch.copyRows h hj state modular newDelta db eb
    (Verify.Core.Scalars.Inverse.coefficient_update _ state.dInvariant state.eInvariant rep.1 dc)
    (Verify.Core.Scalars.Inverse.coefficient_update _ state.dInvariant state.eInvariant rep.2 ec)
  exact ⟨last, mem, d', e', (((prep.trans run).trans el).trans em).trans tail, post⟩

end K256.Proofs.Signing.Composition.Attempt.Inverse
