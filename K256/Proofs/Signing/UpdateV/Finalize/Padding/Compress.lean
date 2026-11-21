import K256.Proofs.Signing.UpdateV.Finalize.Padding.Compress.CallSetup
import K256.Proofs.Signing.UpdateV.Finalize.Padding.Compress.Bytes
import K256.Proofs.Verify.Hash.FinalBlocks.Frame
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

open Compress

theorem compressPadding (outer : Bool) {a : Registers} {m : Ram} {sp : BitVec 64} {msg : ByteArray}
    (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 312 < 2^32)
    (stack : Writable Extracted.programImage m (sp - 344) 656)
    (state : Marked outer a m sp msg) :
    ∃ b t, Reaches (compressStart outer) a m (padEnd outer) b t ∧
      b[4] = ⟨64,sp⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15] → b[i].width = 64) ∧
      RamWriteFrame m t [paddingRegion sp] ∧
      Compression.StateAt t (sp + 72) (digestState msg) := by
  have lo : (sp-344).toNat = sp.toNat-344 := BitVec.toNat_sub_of_le (show (344 : BitVec 64) ≤ sp from depth)
  have ret : (sp-8).toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by omega : 8 ≤ sp.toNat))
  have below : (sp-8-336).toNat = (sp-8).toNat-336 :=
    BitVec.toNat_sub_of_le (show (336 : BitVec 64) ≤ sp-8 from (by omega : 336 ≤ (sp-8).toNat))
  have add (k : Nat) (hk : k ≤ 224) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  have h64 : (sp+64).toNat = sp.toNat+64 := add 64 (by decide)
  have h72 : (sp+72).toNat = sp.toNat+72 := add 72 (by decide)
  have h112 : (sp+112).toNat = sp.toNat+112 := add 112 (by decide)
  have h160 : (sp+160).toNat = sp.toNat+160 := add 160 (by decide)
  obtain ⟨b,step,rsp,rdi,rsi,rdx,widths,saved⟩ := prepareCall outer state (stack.sub (by omega) (by omega))
  let length := bswapSpec (BitVec.ofNat 64 (8*msg.size))
  let retAddr := returnAddress outer
  let staged := callMemory outer m sp msg
  have frame := stage_frame (memStore m (sp+64) length) sp length retAddr (by omega) (by omega)
  have within : RegionsWithin (stageRegions sp) [paddingRegion sp] := by
    intro r hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp only [stageRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only [paddingRegion] <;> omega
  have slot : InRegions [paddingRegion sp] (sp+64) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    dsimp only [InRegion,paddingRegion]
    omega
  have writes : RamWriteFrame m staged [paddingRegion sp] :=
    ((RamWriteFrame.refl m _).memStore length slot).trans frame within
  have win := stack.of_frame writes
  have bytes := stagedBytes (memStore m (sp+64) length) sp length retAddr (finalBlock msg)
    (((stack.sub (by omega) (by omega) : Writable _ _ (sp+112) 64).readable).memStore _ _)
    (FinalBlocks.stagedLast _ _ _ _ state.bytes (stack.sub (by omega) (by omega)).readable)
  have hash : Compression.StateAt staged (sp+72) (compressBlocks initialHash msg) := by
    have apart : RangeApart (sp+64) 8 (sp+72) 32 := RangeApart.of_offsets rfl rfl (by decide)
    apply FinalBlocks.stateOutside ⟨state.hash.1, state.hash.2.write_apart _ _ apart⟩ frame (by omega)
    intro r hr
    simp only [stageRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inl (by change (sp-8).toNat+8 ≤ _; omega)
    · exact Or.inr (by change _ ≤ (sp+112).toNat; omega)
  have word : memLoad staged (sp-8) 64 = retAddr := stage_return _ _ _ _
  have size := finalBlock_size msg
  have contract : Compression.Call b staged (sp-8) (sp+72) (sp+112) (compressBlocks initialHash msg) (finalBlock msg) := by
    refine ⟨rsp,rdi,rsi,by rw [size]; exact rdx,widths,hash,by simpa only [size,staged,callMemory,length,retAddr] using bytes,?_,?_,
      by omega,?_,?_,?_,Or.inr (by omega),Or.inr (by omega)⟩
    · rw [size]; exact (win.sub (by omega) (by omega)).readable
    · exact win.sub (by omega) (by omega)
    · exact win.sub (by omega) (by omega)
    · exact (win.sub (by omega) (by omega)).readable
    · rw [word]; cases outer <;> decide
  obtain ⟨out,run,post⟩ := Compression.execute contract
  have back := ParseSignature.exec_reaches_resume run (resumeFrame outer) [] (by
    rw [post.tag,word]; cases outer <;> rfl)
  refine ⟨out.values,out.store,.step (congrArg (Transfer.next _ []) step) back,?_,?_,?_,?_,?_⟩
  · rw [post.rsp]; congr 1; bv_omega
  · intro i hi
    exact (post.preserved i (by simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (saved i hi)
  · intro i hi
    rw [post.preserved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact widths i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)
  · apply writes.trans post.writes
    intro r hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only [paddingRegion] <;> omega
  · simpa only [compressBlocks_single _ _ size,digestState] using post.state

end K256.Proofs.Signing.UpdateV.Finalize
