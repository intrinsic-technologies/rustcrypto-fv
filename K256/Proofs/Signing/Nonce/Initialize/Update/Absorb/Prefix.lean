import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.First
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Second

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem Absorb.appendPrefix {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (appendAt second) fr a m state) (slots : second = true → Slots fr m)
    (buf : second = true → a[13] = ⟨64, sp fr + 392⟩)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key ByteArray.empty) :
    ∃ b n, Verify.Core.Reaches (appendAt second) a m (Absorb.afterPrefix second input) b n ∧
      Live (Absorb.afterPrefix second input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      (seeded input = true → Absorb.Cursor second fr b 0) ∧
      UpdateV.HmacStateAt n (context fr second) state.key (Absorb.taggedValue second state) := by
  cases second
  · exact Absorb.appendFirstPrefix env roundOk live slots buf ctx
  · exact Absorb.appendSecondPrefix env roundOk live slots buf ctx

end K256.Proofs.Signing.Nonce.Initialize.Update
