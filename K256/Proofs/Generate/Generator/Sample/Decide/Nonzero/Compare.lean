import K256.Spec.Program
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Generate.LIR.Fn10a280.Frame
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Common.Tactic
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

private def compareArgs (a : Vector Value Reg.count) (sp si : BitVec 64) :=
  (((a.set 1 ⟨64, 4⟩).set 2 ⟨64, si⟩).set 4 ⟨64, sp - 16⟩).set 6 ⟨64, 4⟩

private theorem compareEntry {a : Vector Value Reg.count} {m : Ram} {sp si : BitVec 64}
    (rsp : a[4].get 64 = sp) (rsi : a[6].get 64 = si)
    (push : StoreOk Extracted.programImage m (sp - 8) 8 0x10a280 1)
    (call : StoreOk Extracted.programImage (memStore m (sp - 8) (a[0].get 64)) (sp - 16) 8 0x10a28e 5) :
    program.runBlock (dialect Extracted.programImage) ⟨.l10a280, a, m⟩ =
      .call ⟨.l127f50, compareArgs a sp si,
        memStore (memStore m (sp - 8) (a[0].get 64)) (sp - 16) (0x10a293 : BitVec 64)⟩
        (callFrame .l10a293 0x10a293) := by
  have sub : sp - 8 - 8 = sp - 16 := by bv_omega
  cfg_eval [rsp, rsi, sub, push, call]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ j : Fin 53, u[j.val] = v[j.val]) → u = v from
    fun h => Vector.ext fun j hj => h ⟨j, hj⟩)
  intro j
  finite_cases j <;> simp only [compareArgs, Vector.getElem_set] <;> rfl

private def tailArgs (a : Vector Value Reg.count) (sp : BitVec 64) :=
  (a.set 4 ⟨64, sp⟩).set 7 ⟨64, (a[0].get 8).setWidth 64⟩

private theorem compareTail {a : Vector Value Reg.count} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp - 8) (pop : LoadOk m (sp - 8) 8)
    (binary : a[0].get 8 = 0 ∨ a[0].get 8 = 1) :
    program.runBlock (dialect Extracted.programImage) ⟨.l10a293, a, m⟩ =
      .jump ⟨.l127d50, tailArgs a sp, m⟩ := by
  have low : (a[0].get 64).setWidth 8 = a[0].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  have add : sp - 8 + 8 = sp := by bv_omega
  cfg_eval [rsp, pop, add, setWidth_mergeGPR8, low]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ j : Fin 53, u[j.val] = v[j.val]) → u = v from
    fun h => Vector.ext fun j hj => h ⟨j, hj⟩)
  intro j
  finite_cases j <;> simp only [tailArgs, Vector.getElem_set] <;> try rfl
  change Value.mk 64 ((a[0].get 8 &&& 1#8).setWidth 64) = ⟨64, (a[0].get 8).setWidth 64⟩
  rcases binary with h | h <;> rw [h] <;> rfl

theorem compareFour (fr : Activation)
    (left : Readable fr.original fr.rdi 32) (right : Readable fr.original fr.rsi 32)
    (leftApart : Outside [fr.region] fr.rdi 32) (rightApart : Outside [fr.region] fr.rsi 32) :
    Call Extracted.programImage .l10a280 Fn10a280.frameInfo fr [] fun out =>
      (out.values[0].get 8 = 1 ↔ ∀ i < 4,
        memLoad fr.original (wordAddr fr.rdi 64 i) 64 =
          memLoad fr.original (wordAddr fr.rsi 64 i) 64) ∧
      (out.values[0].get 8 = 0 ∨ out.values[0].get 8 = 1) := by
  intro a entry
  change Atom.All _ a _ (Fn10a280.frameAt .l10a280 fr) at entry
  simp only [Fn10a280.frameAt, Fn10a280.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp, df, _, _, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ft, fc,
    readable, ret, retLow, stack, room, align, _⟩ := entry
  change fr.low.toNat + 16 ≤ fr.rsp.toNat at room
  have addr16 : (fr.rsp - 16).toNat = fr.rsp.toNat - 16 := by bv_omega
  let saved := memStore fr.original (fr.rsp - 8) (a[0].get 64)
  let m := memStore saved (fr.rsp - 16) (0x10a293 : BitVec 64)
  have run := compareEntry (m := fr.original) (sp := fr.rsp) (si := fr.rsi) (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 64) si) (by slot_guard using code_l10a280) (by slot_guard using code_l10a280)
  have inside (k : BitVec 64) (lo : 8 ≤ k.toNat) (hi : k.toNat ≤ 16) :
      InRegions [fr.region] (fr.rsp - k) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ _ ∧ _ + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _ + 8 ≤ 2^64
    rw [BitVec.toNat_sub_of_le (show k ≤ fr.rsp by rw [BitVec.le_def]; omega)]
    have := fr.rsp.isLt
    omega
  have written : RamWriteFrame fr.original m [fr.region] :=
    ((RamWriteFrame.refl _ _).memStore _ (inside 8 (by decide) (by decide))).memStore _
      (inside 16 (by decide) (by decide))
  let cmp := {fr with original := m, rsp := fr.rsp - 16, ret := 0x10a293, rdx := fr.rsi, rcx := 4, rsi := 4}
  let b := compareArgs a fr.rsp fr.rsi
  have childRead : Readable m (fr.rsp - 16) 8 := by slot_state region
  have cmpEntry : Atom.All Extracted.programImage b m (K256.Proofs.LIR.Fn127f50.frameAt .l127f50 cmp) := by
    simp only [K256.Proofs.LIR.Fn127f50.frameAt, K256.Proofs.LIR.Fn127f50.frameAtG0, Atom.All, Atom.Holds, b, compareArgs, Fin.getElem_fin, Vector.getElem_set]
    refine ⟨rfl, df, rfl, rfl, bx, bp, rfl, di, r8, r9, r12, r13, r14, r15, mx, ft, fc,
      childRead, memLoad_memStore_same _ _ _ (by decide) (by decide), by change (0x10a293#64).toNat < 2^32; decide, ?_, ?_, trivial⟩
    · change fr.low.toNat ≤ (fr.rsp - 16).toNat
      rw [addr16]
      omega
    · change (fr.rsp - 16).toNat % 16 = 8
      rw [addr16]
      omega
  obtain ⟨o, cmpRun, cmpTag, cmpDone, _, widths, same, eqByte, binary⟩ :=
    ctEq_call Common.fnCode_subset_programImage cmp rfl rfl (left.of_frame written) (right.of_frame written) b cmpEntry
  change o.store = m at same
  rw [← K256.Proofs.LIR.Fn127f50.doneAt_canonical] at cmpDone
  simp only [K256.Proofs.LIR.Fn127f50.doneAt, Atom.All, Atom.Holds] at cmpDone
  obtain ⟨osp, odf, obx, obp, o12, o13, o14, o15, omx, oft, ofc, _⟩ := cmpDone
  have osp' : o.values[4].get 64 = fr.rsp - 8 := by
    apply (congrArg (Value.get 64) osp).trans
    change fr.rsp - 16 + 8 = fr.rsp - 8
    bv_omega
  have jump := compareTail (m := o.store) osp' (by rw [same]; slot_guard using code_l10a293) binary
  let t := tailArgs o.values fr.rsp
  let base := {fr with original := o.store}
  let box := ParseSignature.withArguments base t
  have tw : ParseSignature.ArgumentWidths t := by
    intro ⟨i, hi⟩ h
    have old := widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [t, tailArgs, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] <;>
      first | rfl | exact old
  have boxEntry : Atom.All Extracted.programImage t o.store (Fn127d50.frameAt .l127d50 box) := by
    simp only [Fn127d50.frameAt, Fn127d50.frameAtG10, Atom.All, Atom.Holds]
    have keep (i : Nat) (hi : i < Reg.count := by decide)
        (h4 : 4 ≠ i := by decide) (h7 : 7 ≠ i := by decide) : t[i] = o.values[i] := by
      simp only [t, tailArgs, Vector.getElem_set, h4, h7, ↓reduceIte]
    refine ⟨by simp only [t, tailArgs, Fin.getElem_fin, Vector.getElem_set]; rfl,
      (keep 22).trans odf, ParseSignature.entryArgument tw base 1 (by decide),
      ParseSignature.entryArgument tw base 2 (by decide), (keep 3).trans obx, (keep 5).trans obp,
      ParseSignature.entryArgument tw base 6 (by decide), ParseSignature.entryArgument tw base 7 (by decide),
      ParseSignature.entryArgument tw base 8 (by decide), ParseSignature.entryArgument tw base 9 (by decide),
      (keep 12).trans o12, (keep 13).trans o13, (keep 14).trans o14, (keep 15).trans o15,
      (keep 39).trans omx, (keep 50).trans oft, (keep 51).trans ofc, ?_, ?_, retLow, ?_, ?_, align, trivial⟩
    · rw [same]; exact readable.of_frame written
    · change memLoad o.store fr.rsp 64 = fr.ret
      rw [same, written.memLoad_eq, ret]
      refine ⟨by have := readable.low; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      right
      change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
      omega
    · change Writable Extracted.programImage o.store (fr.rsp - 1) 1
      rw [same]
      slot_state region
    · change fr.low.toNat + 1 ≤ fr.rsp.toNat; omega
  obtain ⟨out, tailRun, tag, doneRegs, boxWrites, finalWidths, byte⟩ :=
    blackBox_call Common.fnCode_subset_programImage box t boxEntry
  refine ⟨out, ParseSignature.exec_call run cmpRun ?_ ?_, tag, doneRegs, ?_, finalWidths, ?_⟩
  · rw [cmpTag]; rfl
  · have resume : (callFrame .l10a293 0x10a293).resume o =
        (⟨.l10a293, o.values, o.store⟩ : Location Value Ram Label signature) := by
      change Location.mk Label.l10a293 ((callFrame .l10a293 0x10a293).resume o).arguments _ = _
      rw [ParseSignature.resume_arguments]
    rw [resume]
    apply Program.Exec.next (next := ⟨⟨.l127d50, t, o.store⟩, []⟩) _ tailRun
    simp only [Program.step, jump, Transfer.next]
    rfl
  · change RamWriteFrame o.store out.store [fr.region] at boxWrites
    rw [same] at boxWrites
    exact written.trans boxWrites fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
  · have byteEq : out.values[0].get 8 = o.values[0].get 8 := by
      apply (congrArg (Value.get 8) byte).trans
      simp only [box, base, ParseSignature.withArguments, t, tailArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
      change (((((o.values[0].get 8).setWidth 64).setWidth 8).setWidth 64).setWidth 8) = _
      simp
    dsimp only
    rw [byteEq]
    refine ⟨eqByte.trans ?_, binary⟩
    change (∀ i < 4, memLoad m (wordAddr fr.rdi 64 i) 64 = memLoad m (wordAddr fr.rsi 64 i) 64) ↔ _
    have preserved (p : BitVec 64) (h : Outside [fr.region] p 32) (i : Nat) (hi : i < 4) :
        memLoad m (wordAddr p 64 i) 64 = memLoad fr.original (wordAddr p 64 i) 64 := by
      apply written.memLoad_eq
      have low := h.1
      have off : (wordAddr p 64 i).toNat = p.toNat + 8 * i := by
        simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, fun r hr => ?_⟩
      · rw [off]; omega
      · rcases h.2 r hr with hl | hr
        · left; rw [off]; omega
        · right; rw [off]; omega
    exact forall_congr' fun i => forall_congr' fun hi => by rw [preserved _ leftApart i hi, preserved _ rightApart i hi]

end K256.Proofs.Generate.Generator.Sample
