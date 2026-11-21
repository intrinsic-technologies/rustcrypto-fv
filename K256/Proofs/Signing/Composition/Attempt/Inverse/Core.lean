import K256.Proofs.Signing.Composition.Attempt.Inverse.Initialize
import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
import K256.Proofs.Signing.Composition.Attempt.Inverse.Finish
import K256.Proofs.Signing.Transfer.Generator
import K256.Proofs.Signing.Transfer.Verify

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Common.Field
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore batchLabel CalleeResult)
open Verify.Core (Registers)
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem execute : CoreExecution := by
  intro a m p k h
  have batches (j : Nat) (hj : j ≤ 10) :
      ∃ b n d e, Reaches .l108e30 a m (batchLabel j) b n ∧
        LoopState a m p k (roundsBefore j) b n d e := by
    induction j with
    | zero =>
      obtain ⟨b,n,run,st⟩ := initializeLoop h
      exact ⟨b,n,0,1,run,st⟩
    | succ j ih =>
      obtain ⟨b,n,d,e,run,st⟩ := ih (by omega)
      obtain ⟨c,t,d',e',step,next⟩ := batch h (by omega) st
      rw [batchLabel, ite_eq_right (by omega : j ≠ 10)] at run
      exact ⟨c,t,d',e',run.trans step,next⟩
  obtain ⟨b,n,d,e,run,st⟩ := batches 10 (by decide)
  obtain ⟨out,last,post⟩ := finish h st
  have ge := Program.Exec.of_sem (run.exec last.sem)
  have ve : Verify.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l108e30,a,m⟩,[]⟩ out := by
    apply Verify.Transfer.Padding.exec Signing.Transfer.Generator.paddingPrefix
    exact Generate.Serialize.Relabel.exec Signing.Transfer.Generator.blocks ge (by rfl)
  exact ⟨out, Generate.Serialize.Relabel.exec Signing.Transfer.VerifyProgram.blocks ve (by rfl), post⟩

end K256.Proofs.Signing.Composition.Attempt.Inverse
