import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Prepare
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Run
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Arithmetic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine.Invert

theorem step (shift : ModularShift) {a b : Registers} {m p : Ram} {sp : Word}
    {s n : Nat} {d e : Int} (h : Entry a m sp s) (state : LoopState a m sp s n b p d e)
    (more : n < 591) :
    (∃ c, Reaches .l1097fe b p .l109948 c p ∧ LoopState a m sp s n c p d e ∧
      (Inverse.model s n).g = 0) ∨
    ∃ c q d' e', let k := count n
      Reaches .l1097fe b p (if n + k = 591 then .l109948 else .l1097fe) c q ∧
        LoopState a m sp s (n + k) c q d' e' := by
  rcases prepare h state more with stop | ⟨c, q, w, path, inner, low, identity, rsp, k, controls, frame, remaining⟩
  · exact Or.inl stop
  have pos : 0 < count n := by unfold count; omega
  have limit : count n ≤ 62 := Nat.min_le_left ..
  obtain ⟨c', run, kept, rows⟩ := runWords (p := q) pos limit inner
  have dl := low.1
  change w.delta.toInt = (Inverse.model s n).delta at dl
  have bd := Generate.Generator.Affine.Invert.Core.Batch.deltaBound n ⟨1, domain.n, s⟩
  change (Inverse.model s n).delta.natAbs ≤ 1 + 2*n at bd
  have delta : w.delta.toInt.natAbs + 2*count n ≤ 1183 := by
    rw [dl]; unfold count; omega
  have odd : (Inverse.model s n).f % 2 = 1 :=
    SafeGcd.divsteps_odd n (s := ⟨1, domain.n, s⟩) (by decide +kernel : (domain.n : Int) % 2 = 1)
  have next : SafeGcd.divsteps (count n) (Inverse.model s n) = Inverse.model s (n + count n) := by
    rw [Inverse.model, ← SafeGcd.divsteps_add]; rfl
  obtain ⟨rep, bound⟩ := SafeGcd.Batch.matrix_represents _ w _ delta limit low identity odd
  have newDelta := (SafeGcd.Batch.matrix_correct _ w _ delta limit low identity).2
  rw [next] at rep newDelta
  obtain ⟨last, ram, d', e', endPath, post⟩ := update shift h state more rows
    ((kept 4 (by decide)).trans rsp) ((congrArg (Value.get 32) (kept 9 (by decide))).trans k)
    (fun i hi => (kept i (List.mem_cons_of_mem 4 (List.mem_cons_of_mem 9 hi))).trans (controls i hi))
    frame remaining newDelta rep bound
  exact Or.inr ⟨last, ram, d', e', (path.trans run).trans endPath, post⟩

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
