import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Arithmetic
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field (BinaryFieldPre)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : BinaryFieldPre s boundary 0x113310 64) (state : DifferenceState s t a b)
    (leftCanonical : a < P256.Spec.Operations.domain.n)
    (rightCanonical : b < P256.Spec.Operations.domain.n) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113ad3 ∧
      Nat256At u (s.regValue .rdi) ((a+b) % P256.Spec.Operations.domain.n) := by
  obtain ⟨keep,flag,value⟩ := selected_sum_mod state leftCanonical rightCanonical
  obtain ⟨n,v,run,frame,rip,output,choice,sum,difference⟩ := choice_stage pre state
  obtain ⟨m,u,tail,final,last,result⟩ := selection_stage (keep := keep) pre frame rip output
    (choice.trans flag)
  refine ⟨n+m,u,run.trans tail,final,last,?_⟩
  rw [sum,difference,value] at result
  exact result

end P256.Proofs.Signing.Core.Iteration.Components.Addition
