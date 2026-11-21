import P256.Proofs.Nonce.Update.Prepare.Assemble.Inner
import P256.Proofs.Nonce.Update.Prepare.Assemble.Outer
import P256.Proofs.Nonce.Update.Prepare.Assemble.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem assemble [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (padded : OuterPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t state := by
  obtain ⟨n, t, innerRun, inner⟩ := Assemble.copy_inner pre padded
  obtain ⟨m, u, outerRun, outer⟩ := Assemble.copy_outer pre inner
  obtain ⟨k, v, copyRun, result⟩ := Assemble.copy_hmac pre outer
  exact ⟨n + m + k, v, (innerRun.trans outerRun).trans copyRun, result⟩

end P256.Proofs.Nonce.Update.Prepare
