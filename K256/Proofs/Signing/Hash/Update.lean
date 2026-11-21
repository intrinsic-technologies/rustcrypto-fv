import K256.Proofs.Signing.Hash.Update.Dispatch
import K256.Proofs.Signing.Hash.Update.Short
import K256.Proofs.Signing.Hash.Update.Long

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

theorem update {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    (rsp : a[4] = ⟨64, sp⟩) (direction : a[22] = ⟨1, 0⟩)
    (count : a[1] = ⟨64, 1⟩) (slice : a[2] = ⟨64, sp + 1136⟩)
    (pointer : memLoad m (sp + 1136) 64 = src)
    (size : memLoad m (sp + 1144) 64 = BitVec.ofNat 64 message.size)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bytes : (⟨src.toNat, message.size⟩ : MemoryRegion).HasBytes m message)
    (input : Readable m src message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (apart : 0 < message.size → src.toNat + message.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (iv : Compression.StateAt m (sp + 552) initialHash)
    (buffered : memLoad m (sp + 551) 8 = 0)
    (blocks : memLoad m (sp + 584) 64 = 0) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1054a6, a, m⟩, []⟩ ⟨⟨.l1055bf, b, t⟩, []⟩ ∧
      Frame sp a b m t ∧ Buffer sp message b t := by
  obtain ⟨c, path, args, keep⟩ := Update.dispatch rsp direction count slice pointer size stack depth limit inputLow buffered
  have run : ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨Update.target message.size, c, m⟩, []⟩ ⟨⟨.l1055bf, b, t⟩, []⟩ ∧
      Frame sp c b m t ∧ Buffer sp message b t := by
    by_cases short : message.size < 64
    · rw [Update.target, ite_eq_left short]
      exact Update.short args short image bytes input stack depth limit inputLow apart iv buffered blocks
    · rw [Update.target, ite_eq_right short]
      exact Update.long args (by omega) image bytes input stack depth limit inputLow (apart (by omega)) iv buffered blocks
  obtain ⟨b, t, steps, frame, buffer⟩ := run
  exact ⟨b, t, path.trans steps, { frame with
    kept := fun i hi => (frame.kept i hi).trans (keep i hi) }, buffer⟩

end K256.Proofs.Signing.Hash
