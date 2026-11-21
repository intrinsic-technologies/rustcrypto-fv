import K256.Proofs.Signing.Hash.Finish.Compress
import K256.Proofs.Signing.Hash.Finish.Bytes

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

open Finish

private abbrev Path (src : Label) (a : Values Value Reg.count) (m : Ram)
    (dst : Label) (b : Values Value Reg.count) (t : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨src,a,m⟩,[]⟩ ⟨⟨dst,b,t⟩,[]⟩

set_option linter.unusedVariables false in
theorem finish {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64} {message : ByteArray}
    (rsp : a[4] = ⟨64, sp⟩) (direction : a[22] = ⟨1, 0⟩)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (ready : Padding sp message a m) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨markTarget message, a, m⟩, []⟩ ⟨⟨.l105758, b, t⟩, []⟩ ∧
      Frame sp a b m t ∧ b[13] = ⟨64,sp+256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → b[i].width = 64) ∧ Compression.StateAt t (sp + 72) (compressBlocks initialHash (bytePadding message)) := by
  let length := bswapSpec (BitVec.ofNat 64 (8 * message.size))
  let first := compressBlocks initialHash message
  let pre := if message.size % 64 < 56 then first else compressBlocks first (paddedBuffer message)
  have base : Finish.State sp a a m m length first :=
    ⟨⟨rsp,direction,fun _ _ => rfl,.refl _ _⟩,ready.state,ready.rbx,ready.length,
     fun i hi => ready.widths i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)⟩
  have lo : (sp-512).toNat = sp.toNat-512 := BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  have dst (k : Nat) (hk : k ≤ 256) : Readable m (sp+BitVec.ofNat 64 k) 64 := by
    have hk' : (sp+BitVec.ofNat 64 k).toNat = sp.toNat+k := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reducePow]; omega
    exact (stack.sub (by omega) (by omega)).readable
  have prepared : ∃ c u, Path (markTarget message) a m .l1056d8 c u ∧
      Finish.State sp a c m u length pre ∧
      (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes u (finalPrefix message) := by
    by_cases small : message.size % 64 < 56
    · simp only [markTarget,pre,small,ite_true]
      exact ⟨a,m,.refl _,base,FinalBlocks.shortPrefix m sp message small ready.bytes⟩
    · simp only [markTarget,pre,small,ite_false]
      obtain ⟨b,t,run,h,_⟩ := Finish.compress base stack depth limit false
        (fun _ => ready.widths 13 (by decide)) (paddedBuffer message) (paddedBuffer_size message)
        (by
          simp only [callMemory,Bool.false_eq_true,ite_false]
          exact stagedBytes m sp (memLoad m (sp+64) 64) (returnAddress false) (paddedBuffer message) (dst 256 (by decide))
            (FinalBlocks.stagedFirst m sp (returnAddress false) message ready.bytes (dst 160 (by decide))))
      have eight : (sp+8).toNat = sp.toNat+8 := by
        simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]; omega
      have window : Writable Extracted.programImage t (sp+8) 56 := (stack.of_frame h.writes).sub (by omega) (by omega)
      obtain ⟨c,step,keep⟩ := clearBlock b t sp (congrArg (Value.get 64) h.rsp) window
      have writes := FinalBlocks.clearPrefix_frame t sp (by omega)
      have state := FinalBlocks.stateOutside h.state writes (by omega) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr; left
        change (sp+8).toNat+56 ≤ sp.toNat+72; omega)
      refine ⟨c,_,run.trans (.step (congrArg (Transfer.next _ []) step) (.refl _)),?_,
        FinalBlocks.clearedPrefix t sp message small window.readable⟩
      refine ⟨⟨(keep 4 (by decide)).trans h.rsp,(keep 22 (by decide)).trans h.df,?_,
        h.writes.trans writes (clearWithin sp depth limit)⟩,state,(keep 3 (by decide)).trans h.rbx,
        (keep 15 (by decide)).trans h.lengthReg,?_⟩
      · intro i hi
        exact (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (h.kept i hi)
      · intro i hi
        exact (congrArg Value.width (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (h.widths i hi)
  obtain ⟨c,u,path,h,headBytes⟩ := prepared
  have bytes := FinalBlocks.stagedLast u sp (returnAddress true) message headBytes
    ((dst 160 (by decide)).of_frame h.writes)
  obtain ⟨d,v,run,out,pointer⟩ := Finish.compress h stack depth limit true (by intro no; contradiction)
    (finalBlock message) (finalBlock_size message)
    (by
      simp only [callMemory,ite_true]
      exact stagedBytes (memStore u (sp+64) length) sp length (returnAddress true) _
        (((dst 256 (by decide)).of_frame h.writes).memStore _ _) bytes)
  have digest : compressBlocks pre (finalBlock message) = compressBlocks initialHash (bytePadding message) := by
    rw [compressBlocks_bytePadding_eq,compressBlocks_single _ _ (finalBlock_size message),finalBlock_eq]
    by_cases small : message.size % 64 < 56
    · simp only [pre,first,small,ite_true]
    · simp only [pre,first,small,ite_false]
      rw [compressBlocks_single _ _ (paddedBuffer_size message)]
      simp only [tailFirst,paddedBuffer,small,ite_false]
  refine ⟨d,v,path.trans run,out.toFrame,pointer rfl,?_,digest ▸ out.state⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rb | bp | r14 | r15
  · obtain rfl : i = 3 := Fin.ext rb
    exact congrArg Value.width out.rbx
  · exact out.widths i (by simp [bp])
  · exact out.widths i (by simp [r14])
  · obtain rfl : i = 15 := Fin.ext r15
    exact congrArg Value.width out.lengthReg

end K256.Proofs.Signing.Hash
