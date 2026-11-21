import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Enter
import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Copy
import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Tag

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem «prefix» [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (prepared : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t state (state.value ++ ⟨#[1]⟩) 0 := by
  obtain ⟨_, u, first, entered⟩ := Prefix.enter pre prepared
  obtain ⟨_, v, second, copied⟩ := Prefix.copy pre entered
  obtain ⟨_, t, third, tagged⟩ := Prefix.tag pre copied
  exact ⟨_, t, (first.trans second).trans third, tagged⟩

end P256.Proofs.Nonce.Update.Seeded.Absorb
