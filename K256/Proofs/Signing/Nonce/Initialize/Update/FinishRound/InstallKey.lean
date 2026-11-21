import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Blocks
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Bytes

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

theorem installRoundKey {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (keyAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (widths : ParseSignature.ArgumentWidths a)
    (digest : (⟨(digestPtr fr second).toNat, 32⟩ : MemoryRegion).HasBytes m (nextKey second input state)) :
    ∃ b n, (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨keyAt second input, a, m⟩, []⟩
      ⟨⟨.l104970, b, n⟩, [Verify.resumeAt (resume second input) (valueReturn second input)]⟩ ∧
      ValueCall second input fr b n ⟨nextKey second input state, state.value⟩ := by
  obtain ⟨b, path, bw, rsp, dst, bx, keep, bxWidth⟩ := keyCallPath second env roundOk live slots widths
  obtain ⟨writes, bytes⟩ := keyCallBytes second env live digest
  obtain ⟨restored, saved⟩ := keyCallFrame second env live slots writes keep bxWidth bytes
  exact ⟨b, _, path, restored, bw, rsp, dst, memLoad_memStore_same _ _ _ (by decide) (by decide), bx, saved⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
