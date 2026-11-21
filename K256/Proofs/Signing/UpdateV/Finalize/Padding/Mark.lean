import K256.Proofs.Signing.UpdateV.Finalize.Padding.Mark.Call
import K256.Proofs.Signing.UpdateV.Finalize.Padding.Copy
import K256.Proofs.Signing.UpdateV.Finalize.Padding.Bytes
import K256.Proofs.Signing.UpdateV.Finalize.Memory
import K256.Proofs.Verify.Hash.Mark.ZeroFill
import K256.Proofs.Verify.Hash.FinalBlocks.Bytes
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Verify.LIR.Fn107a50.Frame

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

set_option maxHeartbeats 500000 in
theorem markPadding (outer : Bool) {a : Registers} {m : Ram} {sp src : BitVec 64} {msg : ByteArray}
    (rsp : a[4] = ⟨64,sp⟩) (df : a[22] = ⟨1,0⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64)
    (source : if outer then src = sp + 208 else a[15].get 64 + 64 = src)
    (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 312 < 2^32)
    (read : Readable m src 104) (above : sp.toNat + (if outer then 208 else 312) ≤ src.toNat)
    (stack : Writable Extracted.programImage m (sp - 344) 656)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (state : Buffered m src msg) (small : msg.size % 64 < 56) :
    ∃ b t, Reaches (padStart outer) a m (compressStart outer) b t ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      RamWriteFrame m t [paddingRegion sp,⟨(sp + 271).toNat,1⟩] ∧
      (outer = false → memLoad t (sp + 271) 8 = 0) ∧ Marked outer b t sp msg := by
  let n := msg.size % 64
  let rem := 63 - n
  let dst := sp+9+BitVec.ofNat 64 n
  let localWrites : List MemoryRegion := [⟨(sp-8).toNat,80⟩]
  let allWrites := [paddingRegion sp,⟨(sp+271).toNat,1⟩]
  let copied := copyMemory outer m sp src
  let marked := Mark.marked copied sp n
  let pushed := memStore marked (sp-8) (Mark.ret outer)
  have nBound : n < 64 := Nat.mod_lt _ (by decide)
  have base : (sp-344).toNat = sp.toNat-344 :=
    BitVec.toNat_sub_of_le (show (344 : BitVec 64) ≤ sp from depth)
  have slot : (sp-8).toNat = sp.toNat-8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by change 8 ≤ sp.toNat; omega))
  have addr (i : Nat) (hi : i ≤ 312) :
      (sp+BitVec.ofNat 64 i).toNat = sp.toNat+i := toNat_add_ofNat sp i (by omega)
  have bufPos : (sp+8).toNat = sp.toNat+8 := addr 8 (by decide)
  have nine : (sp+9).toNat = sp.toNat+9 := addr 9 (by decide)
  have dstPos : dst.toNat = sp.toNat+9+n := by
    dsimp only [dst]
    rw [toNat_add_ofNat _ _ (by omega),nine]
  have markerPos : (sp+8+BitVec.ofNat 64 n).toNat = sp.toNat+8+n := by
    rw [toNat_add_ofNat _ _ (by omega),bufPos]
  have flagPos : (sp+271).toNat = sp.toNat+271 := addr 271 (by decide)
  have hashPos : (sp+72).toNat = sp.toNat+72 := addr 72 (by decide)
  have usedPos : (sp+71).toNat = sp.toNat+71 := addr 71 (by decide)
  have countPos : (sp+104).toNat = sp.toNat+104 := addr 104 (by decide)
  have localSlot (p : BitVec 64) (k : Nat) (lo : (sp-8).toNat ≤ p.toNat)
      (hi : p.toNat+k ≤ (sp-8).toNat+80) : InRegions localWrites p k :=
    ⟨_,List.mem_cons_self,lo,hi,by omega⟩
  have localWithin : RegionsWithin localWrites allWrites := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,by change sp.toNat-344 ≤ (sp-8).toNat; omega,
      by change (sp-8).toNat+80 ≤ sp.toNat-344+520; omega⟩
  have withinStack : RegionsWithin allWrites [⟨(sp-344).toNat,656⟩] := by
    intro r hr
    rcases List.mem_cons.mp hr with h|h
    · subst r
      exact ⟨_,List.mem_cons_self,by change (sp-344).toNat ≤ sp.toNat-344; omega,
        by change sp.toNat-344+520 ≤ (sp-344).toNat+656; omega⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_,List.mem_cons_self,by change (sp-344).toNat ≤ (sp+271).toNat; omega,
        by change (sp+271).toNat+1 ≤ (sp-344).toNat+656; omega⟩
  obtain ⟨buffer,copyFrame,clearFlag⟩ := copyBuffered outer depth limit read above state
  have markerFrame : RamWriteFrame copied marked localWrites :=
    (RamWriteFrame.refl _ _).memStore _ (localSlot _ 1 (by omega) (by omega))
  have pushFrame : RamWriteFrame copied pushed localWrites :=
    markerFrame.memStore _ (localSlot _ 8 (by omega) (by omega))
  have copiedWin := stack.of_frame copyFrame
  have markedWin := copiedWin.of_frame markerFrame
  have pushedWin := copiedWin.of_frame pushFrame
  have innerCode x hx := Common.fnCode_subset_programImage x (code_l107adb x hx)
  have outerCode x hx := Common.fnCode_subset_programImage x (code_l107da7 x hx)
  have inputFrame : RamWriteFrame m (copyInput outer m sp) [⟨(sp+271).toNat,1⟩] := by
    cases outer
    · exact (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _,by omega⟩
    · exact .refl _ _
  have clearOk := ParseSignature.storeOk_of_codeRange (off := 0) (len := 8)
    (stack.sub (a := sp+271) (n := 1) (by omega) (by omega)) innerCode (by decide)
  have copyDst : Writable Extracted.programImage (copyInput outer m sp) (sp+8) 104 :=
    (stack.of_frame inputFrame).sub (by omega) (by omega)
  have apart : (sp+8).toNat + 104 ≤ src.toNat := by cases outer <;> dsimp at above <;> omega
  have copyOk : RepMovsOk Extracted.programImage (copyInput outer m sp) 0 src (sp+8) 13 8
      (if outer then 0x107db9 else 0x107af4) 3 := by
    apply Generate.Generator.Multiply.Prepare.copyGuard (read.of_frame inputFrame) _ (Or.inr apart)
    cases outer
    · exact ParseSignature.storeOk_of_codeRange (off := 25) copyDst innerCode (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 18) copyDst outerCode (by decide)
  have markW : Writable Extracted.programImage copied (sp+8+BitVec.ofNat 64 n) 1 :=
    copiedWin.sub (by omega) (by omega)
  have pushW : Writable Extracted.programImage marked (sp-8) 8 :=
    markedWin.sub (by omega) (by omega)
  have markOk : StoreOk Extracted.programImage copied (sp+8+BitVec.ofNat 64 n) 1
      (if outer then 0x107dd3 else 0x107b0e) 6 := by
    cases outer
    · exact ParseSignature.storeOk_of_codeRange (off := 51) markW innerCode (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 44) markW outerCode (by decide)
  have pushOk : StoreOk Extracted.programImage marked (sp-8) 8
      (if outer then 0x107de6 else 0x107b21) 6 := by
    cases outer
    · exact ParseSignature.storeOk_of_codeRange (off := 70) pushW innerCode (by decide)
    · exact ParseSignature.storeOk_of_codeRange (off := 63) pushW outerCode (by decide)
  have markedImage := Generate.Generator.Affine.Invert.Core.stackImage stack
    ((RamWriteFrame.refl _ _).trans (copyFrame.trans markerFrame localWithin) withinStack) image
  obtain ⟨gotRead,gotTarget⟩ := Fn107a50.callSlots_loaded
    (sections := Extracted.programSections) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    markedImage (0x203e10,0x12a700) (by decide)
  obtain ⟨args,enter,spArg,lenArg,zeroArg,dstArg,remainArg,hashArg,usedArg,countArg,keptArg,widthArg⟩ :=
    Mark.call (sp := sp) outer msg.size (congrArg (Value.get 64) rsp) (congrArg (Value.get 1) df) source
      (fun _ => clearOk) copyOk
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      (by simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using buffer.used)
      (by simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using buffer.count)
      markOk pushOk ⟨gotRead.low,gotRead.present⟩ gotTarget widths
  have remNat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp only [rem]; omega)]
  have fillW : Writable Extracted.programImage pushed dst (BitVec.ofNat 64 rem).toNat :=
    pushedWin.sub (by omega) (by rw [remNat]; dsimp only [rem]; omega)
  have retApart : Outside [ParseSignature.buffer dst (BitVec.ofNat 64 rem).toNat] (sp-8) 8 := by
    refine ⟨by omega,fun r hr => Or.inl ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp-8).toNat+8 ≤ dst.toNat
    omega
  obtain ⟨out,fill,tag,outSp,fillKept,fillFrame,zero⟩ :=
    Verify.Hash.Mark.zeroFill Common.fnCode_subset_programImage spArg lenArg zeroArg dstArg
      (congrArg (Value.get 1) ((keptArg 22 (by decide)).trans df)) fillW
      (LoadOk.of_region pushedWin.readable (by omega) (by omega))
      (show (Mark.ret outer).toNat < 2^32 by cases outer <;> decide)
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) retApart
  change RamWriteFrame pushed out.store [ParseSignature.buffer dst (BitVec.ofNat 64 rem).toNat] at fillFrame
  change ∀ i < (BitVec.ofNat 64 rem).toNat, memByte out.store (dst+BitVec.ofNat 64 i) = 0 at zero
  rw [remNat] at fillFrame zero
  have fillWithin : RegionsWithin [ParseSignature.buffer dst rem] localWrites := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,by change (sp-8).toNat ≤ dst.toNat; omega,
      by change dst.toNat+rem ≤ (sp-8).toNat+80; dsimp only [rem]; omega⟩
  have post := pushFrame.trans fillFrame fillWithin
  have writes := copyFrame.trans post localWithin
  have afterLocal (p : BitVec 64) (k : Nat) (lo : sp.toNat+72 ≤ p.toNat)
      (hi : p.toNat+k < 2^32) : Outside localWrites p k := by
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp-8).toNat+80 ≤ p.toNat
    omega
  have block := bytes_after_fill msg (Mark.ret outer) (by omega) buffer.bytes fillFrame
    ((stack.of_frame writes).readable.sub (by omega) (by omega)) zero
  have hash := stateAfter post (afterLocal (sp+72) 32 (by omega) (by omega))
    (by simpa only [BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using buffer.hash)
  have keepFill (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = args[i] := fillKept i.val (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega) i.isLt
  obtain ⟨b,branch,branchKept⟩ := Mark.branch outer out.values out.store msg.size small
    (congrArg (Value.get 64) ((keepFill _ (by cases outer <;> decide)).trans remainArg))
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      b[i] = args[i] := (branchKept i (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (keepFill i hi)
  have path : Reaches (padStart outer) a m (Mark.branchLabel outer) out.values out.store := by
    refine .step (congrArg (Transfer.next _ []) enter) ?_
    have filled : program.Exec (dialect Extracted.programImage) ⟨⟨.l12a700,args,pushed⟩,[]⟩ out :=
      .done (congrArg (Transfer.next _ []) fill)
    exact ParseSignature.exec_reaches_resume filled (Mark.resume outer) []
      (by rw [tag]; cases outer <;> rfl)
  exact ⟨b,out.store,path.trans branch,
    fun i hi => (keep i (by simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (keptArg i hi),
    writes,fun h => (post.memLoad_eq (afterLocal (sp+271) 1 (by omega) (by omega))).trans (clearFlag h),
    ⟨(branchKept 4 (by decide)).trans outSp,(keep _ (by cases outer <;> decide)).trans hashArg,
      (keep _ (by cases outer <;> decide)).trans usedArg,(keep _ (by cases outer <;> decide)).trans countArg,
      fun i hi => (congrArg Value.width (keep i (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (widthArg i hi),
      hash,FinalBlocks.shortPrefix out.store sp msg small block⟩⟩

end K256.Proofs.Signing.UpdateV.Finalize
