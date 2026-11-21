import P256.Proofs.Signing.Core.Iteration.Candidate.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} (pre : SignPre s boundary)
    (input : Core.Candidate s t state nonce) (rip : t.RIP = 0x10cad9) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cbed ∧ Validated s u state nonce := by
  obtain ⟨n, a, runA, ripA, stateA⟩ := decode pre input rip
  obtain ⟨m, b, runB, ripB, stateB⟩ := select pre stateA ripA
  obtain ⟨k, u, runU, ripU, stateU⟩ := finish pre stateB ripB
  exact ⟨n+m+k,u,(runA.trans runB).trans runU,ripU,stateU⟩

end P256.Proofs.Signing.Core.Iteration.Candidate
