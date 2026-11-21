import K256.Proofs.Generate.Generator.Multiply.Prepare.Execution
import K256.Proofs.Generate.Generator.Multiply.Loop.Execution

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem coreExecution {fr : Activation} {a : Registers} {d : Nat} (entry : CoreEntry fr a d)
    (pos : 0 < d) (bound : d < domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c880, a, fr.original⟩, []⟩ out ∧
      CoreResult fr d out := by
  obtain ⟨b, m, first, split⟩ := splitScalar entry pos bound
  obtain ⟨c, n, next, ready⟩ := prepare (@Radix.execute) (@lookup) (@addCall) entry pos bound split
  obtain ⟨out, run, post⟩ := windowLoop (@fourDoubles) (@lookup) (@addCall) entry pos bound ready
  exact ⟨out, Program.Exec.of_sem ((first.trans next).exec run.sem), post⟩

end K256.Proofs.Generate.Generator.Multiply
