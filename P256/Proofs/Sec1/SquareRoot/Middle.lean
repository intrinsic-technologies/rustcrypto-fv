import P256.Proofs.Sec1.SquareRoot.Middle.Reduction

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem square_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x beta : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11448f) (r14 : t.regValue .r14 = stackPtr s - 248)
    (input : Field.MontgomeryAt t (stackPtr s - 392) x)
    (candidate : Field.MontgomeryAt t (stackPtr s - 248) beta) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11450a ∧
      Field.MontgomeryAt u (stackPtr s - 392) x ∧
      Field.MontgomeryAt u (stackPtr s - 576) beta ∧
      Field.MontgomeryAt u (stackPtr s - 536) (beta*beta % P256.Spec.Operations.domain.p) := by
  obtain ⟨n1,t1,run1,state1⟩ := Middle.prepare_parameters pre state rip r14 input candidate
  obtain ⟨n2,t2,run2,state2⟩ := Middle.prepare_wide pre state1
  obtain ⟨n3,t3,run3,state3⟩ := Middle.wide_call pre state2
  obtain ⟨n4,u,run4,frame,rip4,input4,copy4,square4⟩ := Middle.reduction_call pre state3
  exact ⟨n1+n2+n3+n4,u,((run1.trans run2).trans run3).trans run4,
    frame,rip4,input4,copy4,square4⟩

end P256.Proofs.Sec1.SquareRoot
