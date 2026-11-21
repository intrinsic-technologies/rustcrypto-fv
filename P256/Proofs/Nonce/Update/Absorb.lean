import P256.Proofs.Nonce.Update.Absorb.Prefix
import P256.Proofs.Nonce.Update.Absorb.Empty
import P256.Proofs.Nonce.Update.Absorb.Seeded

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput} (pre : UpdatePre initial boundary state input)
    (prepared : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state input := by
  obtain ⟨first, t, runFirst, tagged⟩ := Absorb.prefix pre.drbg prepared
  have seeds : ∃ fuel u, Advances boundary fuel t u ∧ Absorbed initial u state input := by
    cases input with
    | empty => exact Absorb.empty pre tagged
    | seeded secret reduced => exact Absorb.seeded pre tagged
  obtain ⟨second, u, runSecond, absorbed⟩ := seeds
  exact ⟨first + second, u, runFirst.trans runSecond, absorbed⟩

end P256.Proofs.Nonce.Update
