import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.CopyContext
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.Digest
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.UpdateValue

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem finishRound {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (digestAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key (message second input state)) :
    ∃ b n, Verify.Core.Reaches (digestAt second input) a m (resume second input) b n ∧
      Live (resume second input) fr b n (Drbg.updateRound (tag second) (seed input) state) ∧
      ((!second && seeded input) = true → Slots fr n) := by
  obtain ⟨b, n, copy, copied, saved, ptr, ctx'⟩ := copyRoundContext second env roundOk live slots ctx
  obtain ⟨c, t, finalize, finished, saved', widths, digest⟩ :=
    finalizeRoundContext second env roundOk copied saved ptr ctx'
  obtain ⟨d, u, push, valueCall⟩ := installRoundKey second env roundOk finished saved' widths digest
  obtain ⟨e, v, ret, result⟩ := resumeRoundValue second env valueCall
  exact ⟨e, v, copy.trans (finalize.trans (push.trans ret)), result⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
