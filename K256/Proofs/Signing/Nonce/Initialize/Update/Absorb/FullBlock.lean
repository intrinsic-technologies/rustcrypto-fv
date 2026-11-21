import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.Fill
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.Compress
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.Tail

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem Absorb.appendSecret {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool)
    (env : Environment fr (.seeded secret reduced))
    (live : Live (Absorb.loopAt second) fr a m state) (slots : Slots fr m)
    (cursor : Absorb.Cursor second fr a 0)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key (Absorb.taggedValue second state)) :
    ∃ b n, Verify.Core.Reaches (Absorb.loopAt second) a m (Absorb.loopAt second) b n ∧
      Live (Absorb.loopAt second) fr b n state ∧ Slots fr n ∧ Absorb.Cursor second fr b 16 ∧
      UpdateV.HmacStateAt n (context fr second) state.key (Absorb.taggedValue second state ++ secret) := by
  obtain ⟨b, n, first, live₁, slots₁, regs₁, filled⟩ :=
    Absorb.FullBlock.fill second env live slots cursor ctx
  obtain ⟨c, o, middle, live₂, slots₂, regs₂, hashed⟩ :=
    Absorb.FullBlock.compress second env live₁ slots₁ regs₁ filled
  obtain ⟨d, p, last, result⟩ := Absorb.FullBlock.finish second env live₂ slots₂ regs₂ hashed
  exact ⟨d, p, first.trans (middle.trans last), result⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
