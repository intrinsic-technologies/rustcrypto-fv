import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Entry
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Loops
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Compress
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem prepare {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (start second) fr a m state) (slots : second = true → Slots fr m) :
    ∃ b n, Verify.Core.Reaches (start second) a m (appendAt second) b n ∧
      Live (appendAt second) fr b n state ∧ (second = true → Slots fr n) ∧
      (second = true → b[13] = ⟨64, sp fr + 392⟩) ∧
      UpdateV.HmacStateAt n (context fr second) state.key ByteArray.empty := by
  have _ := roundOk
  obtain ⟨a₁, m₁, r₁, l₁, s₁, idx₁, p₁⟩ := Prepare.enter second env live slots
  obtain ⟨a₂, m₂, r₂, l₂, s₂, _, p₂, _⟩ :=
    Prepare.loop second false env l₁ s₁ idx₁ p₁ (fun h => Bool.noConfusion h)
  obtain ⟨a₃, m₃, r₃, l₃, s₃, idx₃, cursor, p₃, hash⟩ := Prepare.compress second env l₂ s₂ p₂
  obtain ⟨a₄, m₄, r₄, l₄, s₄, keep, p₄, h₄⟩ :=
    Prepare.loop second true env l₃ s₃ idx₃ p₃ (fun _ => hash)
  obtain ⟨b, n, r₅, post⟩ := Prepare.copy second env l₄ s₄ (fun h => keep.trans (cursor h)) p₄ (h₄ rfl)
  exact ⟨b, n, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), post⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
