import K256.Proofs.Signing.Hash.Update.Long.Branch
import K256.Proofs.Signing.Hash.Update.Long.Compress
import K256.Proofs.Signing.Hash.Update.Long.Tail

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

theorem long {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    (args : Slice sp src message.size a) (branch : 64 ≤ message.size)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bytes : (⟨src.toNat, message.size⟩ : MemoryRegion).HasBytes m message)
    (input : Readable m src message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (apart : src.toNat + message.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (iv : Compression.StateAt m (sp + 552) initialHash)
    (_buffered : memLoad m (sp + 551) 8 = 0)
    (blocks : memLoad m (sp + 584) 64 = 0) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l105509, a, m⟩, []⟩ ⟨⟨.l1055bf, b, t⟩, []⟩ ∧
      Frame sp a b m t ∧ Buffer sp message b t := by
  obtain ⟨b, front, saved, count, source, length⟩ := toCompression (m := m) args branch (by omega)
  obtain ⟨c, t, compressed, frame, bound, rbp, ptr, r12, n, slice, memcpy, state, total⟩ :=
    compressSlice args saved count source length image bytes input stack depth limit inputLow apart iv blocks
  obtain ⟨out, u, finish, result⟩ := finishSlice frame bound rbp ptr r12 n slice memcpy state total
    image bytes input stack depth limit inputLow apart
  exact ⟨out, u, front.trans (compressed.trans finish), result⟩

end Update
end K256.Proofs.Signing.Hash
