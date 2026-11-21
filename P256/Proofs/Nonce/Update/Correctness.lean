import P256.Proofs.Nonce.Update.Branch
import P256.Proofs.Nonce.Update.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem update_correct_of_stages [Bindings]
    (prepare : ∀ {initial : RamState} {boundary : ReturnBoundary} {state : State},
      DrbgCalleePre initial boundary 0x109f30 1856 state →
      ∃ fuel s, Advances boundary fuel initial s ∧ Prepared initial s state)
    (absorb : ∀ {initial s : RamState} {boundary : ReturnBoundary} {state : State} {input : UpdateInput},
      UpdatePre initial boundary state input → Prepared initial s state →
      ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state input)
    (zero : ∀ {initial s : RamState} {boundary : ReturnBoundary} {state : State} {input : UpdateInput},
      UpdatePre initial boundary state input → Absorbed initial s state input →
      ∃ fuel t, Advances boundary fuel s t ∧ RoundZeroDone initial t state input)
    (seeded : ∀ {initial s : RamState} {boundary : ReturnBoundary}
      {state : State} {secret reduced : ByteArray},
      UpdateSeededPre initial boundary state secret reduced →
      RoundZeroDone initial s state (.seeded secret reduced) →
      ∃ fuel t, Advances boundary fuel s t ∧
        Finished initial t (updateState true (secret ++ reduced) state))
    {initial : RamState} {boundary : ReturnBoundary} {state : State} {input : UpdateInput}
    (pre : UpdatePre initial boundary state input) :
    ∃ t, DrbgCalleeResult initial t boundary 1856 (updateState input.nonempty input.seed state) := by
  obtain ⟨n, s, first, prepared⟩ := prepare pre.drbg
  obtain ⟨m, t, second, absorbed⟩ := absorb pre prepared
  obtain ⟨k, u, third, updated⟩ := zero pre absorbed
  have execution : Advances boundary (n + m + k) initial u := (first.trans second).trans third
  cases input with
  | empty =>
    obtain ⟨v, last, finished⟩ := finish_empty pre updated
    exact finish pre.toDrbgCalleePre finished ⟨_, execution.trans last⟩
  | seeded secret reduced =>
    obtain ⟨l, v, last, finished⟩ := seeded pre updated
    exact finish pre.toDrbgCalleePre finished ⟨_, execution.trans last⟩

end P256.Proofs.Nonce.Update
