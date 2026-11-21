import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem absorb {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (appendAt second) fr a m state) (slots : second = true → Slots fr m)
    (buf : second = true → a[13] = ⟨64, sp fr + 392⟩)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key ByteArray.empty) :
    ∃ b n, Verify.Core.Reaches (appendAt second) a m (digestAt second input) b n ∧
      Live (digestAt second input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      UpdateV.HmacStateAt n (context fr second) state.key (message second input state) := by
  obtain ⟨b, n, run, next, saved, cursor, hmac⟩ :=
    Absorb.appendPrefix second env roundOk live slots buf ctx
  cases input with
  | empty =>
    refine ⟨b, n, run, next, saved, ?_⟩
    simpa only [message, seed, ByteArray.append_empty, Absorb.taggedValue] using hmac
  | seeded secret reduced =>
    obtain ⟨c, t, first, next', saved', cursor', hmac'⟩ :=
      Absorb.appendSecret second env next (saved rfl) (cursor rfl) hmac
    obtain ⟨d, u, rest, final, saved'', hmac''⟩ :=
      Absorb.appendReduced second env next' saved' cursor' hmac'
    exact ⟨d, u, run.trans (first.trans rest), final, fun _ => saved'', hmac''⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
