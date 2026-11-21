import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Sample.Decode.Scalar.Entry
import K256.Proofs.Generate.Generator.Sample.Decode.Scalar.Return
import K256.Proofs.Generate.Generator.Sample.State
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Generate.LIR.Fn109e60.Frame
import K256.Proofs.Generate.Sampling.Predicate

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem decodeScalar (fr : Activation)
    (src : Readable fr.original fr.rsi 32)
    (dst : Writable Extracted.programImage fr.original fr.rdi 33)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 32)
    (dstApart : Outside [ParseSignature.callStack fr] fr.rdi 33) :
    Call Extracted.programImage .l109e60 Fn109e60.frameInfo fr [⟨fr.rdi.toNat, 33⟩] fun out =>
      let w := Common.scalarWord fr.original fr.rsi
      WordsAt out.store fr.rdi 64 (Vector.ofFn fun i : Fin 4 => w i.val) ∧
      memLoad out.store (fr.rdi + 32) 8 = (Sampling.orderFlag (w 0) (w 1) (w 2) (w 3)).setWidth 8 := by
  intro a entry
  change Atom.All _ a _ (Fn109e60.frameAt .l109e60 fr) at entry
  let w := Common.scalarWord fr.original fr.rsi
  obtain ⟨b, m, run, flag, sp, bx, r13, r12, r15, r14, keep, widths, written, retBox, saved⟩ :=
    scalarEntry fr a entry src srcApart
  simp only [Fn109e60.frameAt, Fn109e60.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨_, df, _, _, _, bp, _, _, _, _, _, _, _, _, mx, ft, fc, readRet, originalRet,
    retLow, writeStack, room, align, _⟩ := entry
  let base := {fr with original := m, rsp := fr.rsp - 64, ret := 0x109f32, rbx := fr.rdi, r12 := w 1, r13 := w 0, r14 := w 3, r15 := w 2}
  let box := ParseSignature.withArguments base b
  have subAddr (k : Nat) (hk : k ≤ 65) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have modK : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, modK]; omega), modK]
  have boxAddr : box.rsp.toNat = fr.rsp.toNat - 64 := subAddr 64 (by decide)
  have window := writeStack.of_frame written
  have boxRead : Readable m box.rsp 8 := by
    have ha : (fr.rsp - 65).toNat = fr.rsp.toNat - 65 := subAddr 65 (by decide)
    apply window.readable.sub <;> rw [ha, boxAddr] <;> omega
  have boxWrite : Writable Extracted.programImage m (box.rsp - 1) 1 := by
    have addr : box.rsp - 1 = fr.rsp - 65 := by change fr.rsp - 64 - 1 = _; bv_omega
    rw [addr]
    exact window.sub (Nat.le_refl _) (by omega)
  have boxEntry : Atom.All Extracted.programImage b m (Fn127d50.frameAt .l127d50 box) := by
    simp only [Fn127d50.frameAt, Fn127d50.frameAtG10, Atom.All, Atom.Holds]
    refine ⟨sp, (keep 22 (by decide)).trans df, ParseSignature.entryArgument widths base 1 (by decide),
      ParseSignature.entryArgument widths base 2 (by decide), bx, (keep 5 (by decide)).trans bp,
      ParseSignature.entryArgument widths base 6 (by decide), ParseSignature.entryArgument widths base 7 (by decide),
      ParseSignature.entryArgument widths base 8 (by decide), ParseSignature.entryArgument widths base 9 (by decide),
      r12, r13, r14, r15, (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
      (keep 51 (by decide)).trans fc, boxRead, retBox, by change (0x109f32#64).toNat < 2^32; decide, boxWrite, ?_, ?_, trivial⟩
    · change fr.low.toNat + 1 ≤ box.rsp.toNat
      rw [boxAddr]
      omega
    · rw [boxAddr]
      omega
  obtain ⟨o, boxRun, tag, regs, boxWrites, outWidths, outFlag⟩ :=
    blackBox_call Common.fnCode_subset_programImage box b boxEntry
  rw [← Fn127d50.doneAt_canonical] at regs
  simp only [Fn127d50.doneAt, Atom.All, Atom.Holds] at regs
  obtain ⟨osp, odf, obx, obp, o12, o13, o14, o15, omx, oft, ofc, _⟩ := regs
  have stackFrame : RamWriteFrame fr.original o.store [fr.region] := by
    apply written.trans boxWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
    change fr.low.toNat + (box.rsp.toNat - fr.low.toNat) ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    rw [boxAddr]
    omega
  have savedAt (k r : Nat) (h : (k,r) ∈ [(40,3), (32,12), (24,13), (16,14), (8,15)]) :
      memLoad o.store (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
    have hk : k ≤ 40 := by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h; omega
    rw [boxWrites.memLoad_eq]
    · exact saved k r h
    refine ⟨?_, ?_⟩
    · rw [subAddr k (by omega)]
      have := readRet.low
      omega
    · intro reg hreg
      obtain rfl := List.mem_singleton.mp hreg
      right
      change fr.low.toNat + (box.rsp.toNat - fr.low.toNat) ≤ _
      rw [boxAddr, subAddr k (by omega)]
      omega
  have retAt : memLoad o.store fr.rsp 64 = fr.ret := by
    rw [stackFrame.memLoad_eq, originalRet]
    refine ⟨by have := readRet.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
    omega
  have atReturn : Atom.All Extracted.programImage o.values o.store (Fn109e60.frameAt .l109f32 fr) := by
    simp only [Fn109e60.frameAt, Fn109e60.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨?_, odf, obx, obp, omx, oft, ofc, savedAt 40 3 (by decide), savedAt 32 12 (by decide),
      savedAt 24 13 (by decide), savedAt 16 14 (by decide), savedAt 8 15 (by decide),
      readRet.of_frame stackFrame, retAt, retLow, writeStack.of_frame stackFrame, room, align, trivial⟩
    rw [osp]
    congr 1
    change fr.rsp - 64 + 8 = fr.rsp - 56
    bv_omega
  have flagAt : o.values[0].get 8 = (Sampling.orderFlag (w 0) (w 1) (w 2) (w 3)).setWidth 8 := by
    rw [outFlag]
    change ((b[7].get 64).setWidth 8 |>.setWidth 64 |>.setWidth 8) = _
    rw [flag]
    simp [Value.get, w]
  obtain ⟨out, finish, outTag, doneRegs, stores, output⟩ :=
    scalarReturn fr _ _ atReturn (dst.of_frame stackFrame) dstApart outWidths w _ flagAt o13 o12 o15 o14
  refine ⟨out, ParseSignature.exec_call run boxRun ?_ ?_, outTag, doneRegs, ?_, output⟩
  · rw [tag]
    rfl
  · have resume : (callFrame .l109f32 0x109f32).resume o =
        (⟨.l109f32, o.values, o.store⟩ : Location Value Ram Label signature) := by
      change Location.mk Label.l109f32 ((callFrame .l109f32 0x109f32).resume o).arguments _ = _
      rw [ParseSignature.resume_arguments]
    rw [resume]
    exact finish
  · have subset {r : MemoryRegion} {rs : List MemoryRegion} (mem : r ∈ rs) : RegionsWithin [r] rs := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨_, mem, Nat.le_refl _, Nat.le_refl _⟩
    exact ((RamWriteFrame.refl _ _).trans stackFrame (subset (List.mem_cons_self ..))).trans stores
      (subset (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end K256.Proofs.Generate.Generator.Sample
