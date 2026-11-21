import K256.Proofs.Signing.UpdateV.Prepare
import K256.Proofs.Signing.UpdateV.Finalize
import K256.Proofs.Signing.UpdateV.Return

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

theorem execution {fr : Activation} {a : Values Value Reg.count} {key value : ByteArray}
    (entry : Atom.All Extracted.programImage a fr.original (Fn104970.frameAt .l104970 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32) (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (k : (⟨fr.rdi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original key)
    (v : (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes fr.original value) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104970, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn104970.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat + 32, 32⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧
      (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes out.store
        (HMAC.hmac SHA256.hashBytes 64 key value) := by
  obtain ⟨b, m, prepared, frame, ctx, state⟩ :=
    prepare entry image low depth limit dataLow apart writable k v
  obtain ⟨c, t, finished, frame', widths, digest⟩ :=
    finalize image low depth limit k.1 v.1 frame ctx state
  obtain ⟨out, returned, post⟩ :=
    returnPath low depth limit dataLow apart writable frame' widths digest
  exact ⟨out, Program.Exec.of_sem ((prepared.trans finished).exec returned.sem), post⟩

end K256.Proofs.Signing.UpdateV
