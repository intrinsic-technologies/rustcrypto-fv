import K256.Proofs.Ecdh.Multiply.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Export

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

local macro "peer_export_bounds " e:ident : tactic =>
  `(tactic| (
    try dsimp only [exportWrites,copySrc,copyDst,ite_true,ite_false,Bool.false_eq_true]
    peer_acc_bounds using $e))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem peerExportOne (first : Bool) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    {p : Standards.SECG.ECC.Curve.Point} (entry : PeerCoreEntry fr initial d peer)
    (s : State (copySite first) fr a m)
    (table : TableAt m (copySrc first fr) p)
    (pointer : memLoad m (sp fr+216) 64 = fr.rcx)
    (fnPtr : first = false → a[3].get 64 = 0x12a820) (tabPtr : first = false → a[5] = ⟨64,fr.rcx⟩)
    (srcPtr : first = false → a[13].get 64 = sp fr+0x490) :
    ∃ b n, Reaches (copySite first) a m (copyResume first) b n ∧
      State (copyResume first) fr b n ∧ TableAt n (copyDst first fr) p ∧
      RamWriteFrame m n (exportWrites first fr) ∧ b[3].get 64 = 0x12a820 ∧
      b[5] = ⟨64,fr.rcx⟩ ∧ ∀ j : Fin Reg.count, j.val ∈ [12,13,14,15] → b[j] = a[j] := by
  have srcLayout : Fn11c880.frameAt (copySite first) fr = Fn11c880.frameAt .l11c9e7 fr := by cases first <;> rfl
  have dstLayout : Fn11c880.frameAt (copyResume first) fr = Fn11c880.frameAt .l11c9e7 fr := by cases first <;> rfl
  obtain ⟨rsp,df,stack⟩ := Accumulator.currentStack s srcLayout
  have slot : Writable Extracted.programImage m (sp fr-8) 8 := by apply stack.sub <;> peer_export_bounds entry
  have read : Readable m (sp fr+216) 8 := by apply stack.readable.sub <;> peer_export_bounds entry
  obtain ⟨b,call,fnPtr,tabPtr,count,dst,src,keep⟩ := exportBlock first
    (congrArg (Value.get 64) rsp) slot s.widths s.savedWidths read pointer fnPtr tabPtr srcPtr
  let tag := copyTag first
  let nm := memStore m (sp fr-8) tag
  have push := Accumulator.peerPushFrame entry m tag
  have allSlots := entry.tableWrite.of_frame s.frame
  have write : Writable Extracted.programImage m (copyDst first fr) 960 := by
    apply allSlots.sub <;> cases first <;> peer_export_bounds entry
  have rd : Readable m (copySrc first fr) 960 := by apply stack.readable.sub <;> cases first <;> peer_export_bounds entry
  have oldAtoms := s.atoms
  rw [srcLayout] at oldAtoms
  have align : fr.rsp.toNat % 16 = 8 := oldAtoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have tab := table.of_frame push (by cases first <;> peer_export_bounds entry)
  have tagVal := memLoad_memStore_same m (sp fr-8) tag (by decide) (by decide)
  let dest := copyDst first fr
  let srcBase := copySrc first fr
  have single : RamWriteFrame nm (memCopy nm dest srcBase 960) [⟨dest.toNat,960⟩] :=
    Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _) ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by
      change (copyDst first fr).toNat + 960 ≤ 2^64; cases first <;> peer_export_bounds entry⟩
  have outside : Outside [⟨dest.toNat,960⟩] (sp fr-8) 8 := by
    dsimp only [dest]; cases first <;> peer_export_bounds entry
  have postSlot := (slot.readable.of_frame push).of_frame single
  have load : LoadOk (memCopy nm dest srcBase 960) (sp fr-8) 8 := LoadOk.of_region postSlot (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨out,run,ret,mem,widths,outSp,regs⟩ := Accumulator.copyTable
    dst src count (congrArg (Value.get 64) call.rsp) (congrArg (Value.get 1) ((call.control 22 (by decide)).trans df))
    (by cases first <;> peer_export_bounds entry) call.widths (rd.of_frame push) (write.of_frame push)
    (by cases first <;> peer_export_bounds entry) load ((single.memLoad_eq outside).trans tagVal)
    (by cases first <;> decide)
  have full : RamWriteFrame m out.store (exportWrites first fr) := by
    rw [mem]
    exact ((RamWriteFrame.refl m _).trans push (by cases first <;> peer_export_bounds entry)).trans single
      (by dsimp only [dest]; cases first <;> peer_export_bounds entry)
  have whole := s.frame.trans full (by cases first <;> peer_export_bounds entry)
  have same (j : Fin Reg.count) (hj : j.val ∈ Activation.calleeSavedNumbers) :
      out.values[j] = b[j] := regs j (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj ⊢; omega)
  have ctrl (j : Fin Reg.count) (hj : j.val ∈ [4,22,39,50,51]) : out.values[j] = a[j] := by
    rcases List.mem_cons.mp hj with eq|h
    · obtain rfl : j = 4 := Fin.ext eq
      change out.values[4] = ⟨64,sp fr - 8 + 8⟩ at outSp
      exact (by simpa only [BitVec.sub_add_cancel] using outSp : out.values[4] = ⟨64,sp fr⟩).trans rsp.symm
    · exact (regs j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans (call.control j h)
  have atoms := frameAtoms s.atoms srcLayout dstLayout full (by cases first <;> peer_export_bounds entry)
    (by have := entry.room; omega) (entry.loaded_of_frame whole) ctrl
  refine ⟨_,_,Sample.reachesAfterSampleCall call.step run ret [],⟨atoms,widths,?_,whole,?_⟩,?_,full,?_,?_,?_⟩
  · exact fun j h => (congrArg Value.width (same j h)).trans (call.saved j h)
  · apply s.locals.of_frame full
    intro kv h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> cases first <;> peer_export_bounds entry
  · rw [mem]; exact tab.memCopy
  · exact (congrArg (Value.get 64) (same 3 (by decide))).trans fnPtr
  · exact (same 5 (by decide)).trans tabPtr
  · exact fun j h => (same j (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans (keep j h)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
