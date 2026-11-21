import K256.Proofs.Signing.Hash.Finish.Frame
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Hash.Finish

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

structure State (sp : Word) (entry a : Values Value Reg.count) (original m : Ram)
    (length : Word) (hash : Array UInt32) : Prop extends Frame sp entry a original m where
  state : Compression.StateAt m (sp+72) hash
  rbx : a[3] = ⟨64,sp+72⟩
  lengthReg : a[15] = ⟨64,length⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [5,12,14] → a[i].width = 64

theorem compress {sp : Word} {entry a : Values Value Reg.count} {original m : Ram}
    {length : Word} {hash : Array UInt32}
    (h : State sp entry a original m length hash)
    (stack : Writable Extracted.programImage original (sp-512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat+1160 < 2^32)
    (last : Bool) (r13 : last = false → a[13].width = 64)
    (block : ByteArray) (size : block.size = 64)
    (bytes : (⟨(sp+256).toNat,64⟩ : MemoryRegion).HasBytes (callMemory last m sp length) block) :
    ∃ (b : Values Value Reg.count), ∃ t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨callSite last,a,m⟩,[]⟩ ⟨⟨resumeSite last,b,t⟩,[]⟩ ∧
      State sp entry b original t length (compressBlocks hash block) ∧
      (last = true → b[13] = ⟨64,sp+256⟩) := by
  have len : a[15].get 64 = length := congrArg (Value.get 64) h.lengthReg
  have lo : (sp-512).toNat = sp.toNat-512 := BitVec.toNat_sub_of_le (show (512 : Word) ≤ sp from depth)
  have ret : (sp-8).toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (show (8 : Word) ≤ sp from (by omega : 8 ≤ sp.toNat))
  have ha (n : Nat) (hn : n ≤ 320) : (sp+BitVec.ofNat 64 n).toNat = sp.toNat+n := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  obtain ⟨b,step,rsp,rdi,rsi,rdx,w13,pointer,saved⟩ := prepareCall last a m sp
    (congrArg (Value.get 64) h.rsp) (congrArg (Value.get 64) h.rbx) r13
    ((stack.of_frame h.writes).sub (by omega) (by omega))
  rw [len] at step
  have writes := preparedWrites last m sp length depth limit
  have within : RegionsWithin (regions sp) (regions sp) := fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩
  have allWrites := h.writes.trans writes within
  have win := stack.of_frame allWrites
  have word := preparedReturn last m sp length
  have w72 : (sp+72).toNat = sp.toNat+72 := ha 72 (by decide)
  have w256 : (sp+256).toNat = sp.toNat+256 := ha 256 (by decide)
  have contract : Compression.Call b (callMemory last m sp length) (sp-8) (sp+72) (sp+256) hash block := by
    refine ⟨rsp,rdi,rsi,by rw [size]; exact rdx,?_,preparedState last m sp length h.state (by omega) (by omega),
      by simpa only [size] using bytes,?_,?_,by omega,?_,?_,?_,Or.inr (by omega),Or.inr (by omega)⟩
    · intro ⟨i,hi⟩ mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact w13
        | exact (congrArg Value.width (saved _ (by decide +revert))).trans (congrArg Value.width h.rbx)
        | exact (congrArg Value.width (saved _ (by decide +revert))).trans (congrArg Value.width h.lengthReg)
        | exact (congrArg Value.width (saved _ (by decide +revert))).trans (h.widths _ (by decide +revert))
    · rw [size]; exact (win.sub (by omega) (by omega)).readable
    · exact win.sub (by omega) (by omega)
    · have offset : (sp-8-336).toNat = (sp-8).toNat-336 :=
        BitVec.toNat_sub_of_le (show (336 : Word) ≤ sp-8 from (by omega : 336 ≤ (sp-8).toNat))
      exact win.sub (by omega) (by omega)
    · exact (win.sub (by omega) (by omega)).readable
    · rw [word]; cases last <;> decide
  obtain ⟨out,run,post⟩ := Compression.execute contract
  have back := ParseSignature.exec_reaches_resume run (resumeFrame last) [] (by
    rw [post.tag,word]; cases last <;> rfl)
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,14,15,22,39,50,51]) :
      out.values[i] = a[i] := (post.preserved i (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (saved i hi)
  refine ⟨out.values,out.store,.step (congrArg (Transfer.next _ []) step) back,
    ⟨⟨?_,(keep 22 (by decide)).trans h.df,?_,allWrites.trans post.writes (calleeWithin sp depth limit)⟩,
    post.state,(keep 3 (by decide)).trans h.rbx,(keep 15 (by decide)).trans h.lengthReg,?_⟩, fun lastBlock => (post.preserved 13 (by decide)).trans (pointer lastBlock)⟩
  · rw [post.rsp]; congr 1; change sp-8+8 = sp; bv_omega
  · intro i hi
    exact (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (h.kept i hi)
  · intro i hi
    exact (congrArg Value.width (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (h.widths i hi)

end K256.Proofs.Signing.Hash.Finish
