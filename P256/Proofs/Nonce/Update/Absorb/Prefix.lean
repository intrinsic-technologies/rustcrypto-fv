import P256.Proofs.Nonce.Update.Absorb.Prefix.Enter
import P256.Proofs.Nonce.Update.Absorb.Prefix.Copy
import P256.Proofs.Nonce.Update.Absorb.Prefix.Tag

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem «prefix» [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (prepared : Prepared initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Tagged initial t state := by
  obtain ⟨first, t, runFirst, entered⟩ := Prefix.enter pre prepared
  obtain ⟨second, u, runSecond, copied⟩ := Prefix.copy pre entered
  obtain ⟨third, v, runThird, tagged⟩ := Prefix.tag pre copied
  exact ⟨first + second + third, v, (runFirst.trans runSecond).trans runThird, tagged⟩

end P256.Proofs.Nonce.Update.Absorb
