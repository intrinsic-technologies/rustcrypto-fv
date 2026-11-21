import K256.Proofs.Ecdh.Affine.Inverse.Contract
import K256.Proofs.Ecdh.Affine.Inverse.Zero.Initialize
import K256.Proofs.Ecdh.Affine.Inverse.Zero.Batch
import K256.Proofs.Ecdh.Affine.Inverse.Zero.Finish

namespace K256.Proofs.Ecdh.Affine.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

open K256.Proofs.Generate.Generator.Affine.Invert K256.Proofs.Generate.Generator.Affine

theorem zeroCoreExecution : ZeroCoreExecution := by
  intro a m sp w rsp rcx rdx rsi rdi r8 df widths image low high aligned sr1 s1 sr2 s2 apart stack src dst ret words input
  have h : Zero.ZeroEntry a m sp ⟨0, by decide +kernel⟩ w := ⟨rsp, rcx, rdx, rsi, rdi, r8, df, widths, image, low, high,
    aligned, sr1, s1, sr2, s2, apart, stack, src, dst, ret, words, input, rfl⟩
  have batches (j : Nat) (hj : j ≤ 10) :
      ∃ b p d e, Reaches .l108e30 a m (Core.batchLabel j) b p ∧
        Zero.ZeroLoopState a m sp ⟨0, by decide +kernel⟩ (Core.roundsBefore j) b p d e := by
    induction j with
    | zero =>
      obtain ⟨b, p, path, init⟩ := Zero.initializeLoop h
      exact ⟨b, p, 0, 1, path, init⟩
    | succ j ih =>
      have lt : j < 10 := by omega
      obtain ⟨b, p, d, e, steps, state⟩ := ih (by omega)
      obtain ⟨c, q, d', e', run, post⟩ := Zero.batch h lt state
      rw [Core.batchLabel, ite_eq_right (by omega : j ≠ 10)] at steps
      exact ⟨c, q, d', e', steps.trans run, post⟩
  obtain ⟨b, p, d, e, steps, state⟩ := batches 10 (by decide)
  obtain ⟨out, he, post⟩ := Zero.finish h state
  exact ⟨out, Program.Exec.of_sem (steps.exec he.sem), post⟩

end K256.Proofs.Ecdh.Affine.Inverse
