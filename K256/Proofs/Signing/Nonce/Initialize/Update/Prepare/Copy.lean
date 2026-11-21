import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Execution
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Hmac

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

theorem copy {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second true) fr a m state) (slots : second = true → Slots fr m)
    (cursor : second = true → a[13] = ⟨64, sp fr + 392⟩)
    (bytes : (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes m (UpdateV.keyPad state.key 0x5c))
    (hash : Compressed fr second m state.key) :
    ∃ b n, Verify.Core.Reaches (exitLabel second true) a m (appendAt second) b n ∧
      Live (appendAt second) fr b n state ∧ (second = true → Slots fr n) ∧
      (second = true → b[13] = ⟨64, sp fr + 392⟩) ∧
      UpdateV.HmacStateAt n (context fr second) state.key ByteArray.empty := by
  obtain ⟨b, run, rsp, kept⟩ := copyExecute second env live
  obtain ⟨next, saved⟩ := copyLive second env live slots rsp kept
  exact ⟨b, copied fr second m, run, next, saved, fun h =>
    (kept 13 (by decide)).trans (cursor h), copyHmac second env live bytes hash⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
