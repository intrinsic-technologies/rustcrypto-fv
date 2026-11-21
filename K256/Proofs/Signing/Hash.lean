import K256.Proofs.Signing.Hash.Update
import K256.Proofs.Signing.Hash.Mark
import K256.Proofs.Signing.Hash.Finish
import K256.Proofs.Signing.Hash.Memory

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

theorem digest {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
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
    ∃ b m', (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1054a6, a, m⟩, []⟩ ⟨⟨.l105758, b, m'⟩, []⟩ ∧
      b[4] = ⟨64, sp⟩ ∧ b[22] = ⟨1, 0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m m' (regions sp) ∧ b[13] = ⟨64,sp+256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → b[i].width = 64) ∧
      Compression.StateAt m' (sp + 72) (compressBlocks initialHash (bytePadding message)) := by
  obtain ⟨b,t,u,f,buf⟩ := update rsp direction count slice pointer size image bytes input stack
    depth limit inputLow apart iv buffered blocks
  have st := stack.of_frame f.writes
  have im := imageAfter depth stack f.writes image
  obtain ⟨c,v,z,g,pad⟩ := mark f.rsp f.df im st depth limit buf
  obtain ⟨d,w,k,h,pointerOut,widthsOut,out⟩ := finish g.rsp g.df (imageAfter depth st g.writes im)
    (st.of_frame g.writes) depth limit pad
  have within : RegionsWithin (regions sp) (regions sp) :=
    fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
  exact ⟨d, w, u.trans (z.trans k), h.rsp, h.df,
    fun i hi => (h.kept i hi).trans ((g.kept i hi).trans (f.kept i hi)),
    (f.writes.trans g.writes within).trans h.writes within, pointerOut, widthsOut, out⟩

end K256.Proofs.Signing.Hash
