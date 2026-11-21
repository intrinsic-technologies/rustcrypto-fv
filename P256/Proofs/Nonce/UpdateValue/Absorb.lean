import P256.Proofs.Nonce.UpdateValue.Absorb.Head
import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer
import P256.Proofs.Nonce.UpdateValue.Absorb.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (prepared : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state := by
  obtain ⟨u, runU, entered⟩ := Absorb.head pre prepared
  obtain ⟨n, v, runV, buffered⟩ := Absorb.buffer pre entered
  obtain ⟨m, t, runT, absorbed⟩ := Absorb.copy pre buffered
  exact ⟨4 + (n + m), t, runU.trans (runV.trans runT), absorbed⟩

end P256.Proofs.Nonce.UpdateValue
