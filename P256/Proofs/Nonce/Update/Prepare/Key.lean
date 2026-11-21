import P256.Proofs.Nonce.Update.Prepare.Key.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem key [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (saved : Saved initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Keyed initial t state := by
  obtain ⟨setupFuel, u, setupRun, args⟩ := Key.arguments pre saved
  obtain ⟨fuel, t, run, ready, effect⟩ := Key.call pre args
  exact ⟨setupFuel + fuel, t, setupRun.trans run, Key.keyed pre args ready effect⟩

end P256.Proofs.Nonce.Update.Prepare
