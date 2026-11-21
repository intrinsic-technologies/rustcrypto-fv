import P256.Proofs.Nonce.UpdateValue.Prepare.Key.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem key [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (saved : Saved initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Keyed initial t state := by
  obtain ⟨fuel, t, run, ready, effect⟩ := Key.call pre saved
  exact ⟨fuel, t, run, Key.keyed pre saved ready effect⟩

end P256.Proofs.Nonce.UpdateValue.Prepare
