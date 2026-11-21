import K256.Proofs.Signing.Affine.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core
import K256.Proofs.Generate.Generator.Affine.Invert.PackCall.Memory
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC
open K256.Proofs.Generate.Generator.Affine
open Generate.Generator.Affine.Invert

theorem invertZ {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10ed05 fr a m)
    (h : Coordinates m fr.rsi x y z) (hn : Normalized fr m z) (nz : z.val ≠ 0) :
    ∃ b m', Reaches .l10ed05 a m .l10ed84 b m' ∧ CallState .l10ed84 fr b m' ∧
      Coordinates m' fr.rsi x y z ∧ Inverted fr m' z := by
  obtain ⟨u, input, widths, zval⟩ := hn
  have atoms := s.atoms
  change Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10ed05 fr) at atoms
  simp only [Fn10fe50.frameAt, Fn10fe50.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, r3, r5, r12, r13, r14, r15, r39, r50, r51, s48, s40, s32, s24, s16, s8,
    retRead, ret, retLow, win, room, align, _, _, _, _, got, _⟩ := atoms
  have stackRoom : 976 ≤ fr.rsp.toNat := by omega
  have high := s.source.low
  have above := s.srcAbove
  let q : Word := fr.rsp - 232
  let sp : Word := q - 8
  let w := PackCall.packed u
  let m₁ := PackCall.packedStore m q w
  have spEq : sp = fr.rsp - 240 := by dsimp only [sp, q]; bv_omega
  have winEq : sp - 736 = fr.rsp - 976 := by rw [spEq]; bv_omega
  have outEq : sp + 96 = fr.rsp - 144 := by rw [spEq]; bv_omega
  have statusEq : sp + 128 = fr.rsp - 112 := by rw [spEq]; bv_omega
  have argEq : sp + 8 = q := by dsimp only [sp]; bv_omega
  have srcEq : q + 88 = fr.rsp - 144 := by dsimp only [q]; bv_omega
  have spNat : sp.toNat = fr.rsp.toNat - 240 := by
    rw [spEq]
    exact sub_toNat stackRoom 240 (by decide)
  have winNat : (fr.rsp - 976).toNat = fr.rsp.toNat - 976 :=
    sub_toNat stackRoom 976 (by decide)
  have outNat : (fr.rsp - 144).toNat = fr.rsp.toNat - 144 :=
    sub_toNat stackRoom 144 (by decide)
  have subWindow {n : Nat} (hn : n ≤ 240) : Writable Extracted.programImage m sp n :=
    win.sub (by omega) (by omega)
  have packWin : Writable Extracted.programImage m (q - 8) 40 := subWindow (by decide)
  have wf := PackCall.packedStore_frame m q w packWin.readable.low
  have packFrame : RamWriteFrame m m₁ [scratch fr.rsp] :=
    (RamWriteFrame.refl _ _).trans wf (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      change (fr.rsp - 976).toNat ≤ sp.toNat ∧ sp.toNat + 40 ≤ (fr.rsp - 976).toNat + 976
      omega)
  have loaded := scratch_image win packFrame s.image
  have gotSlots := Fn10fe50.callSlots_loaded
    (show rodataSection ∈ Extracted.programSections by simp [rodataSection, Extracted.programSections])
    loaded
  obtain ⟨gotRead1, gotVal1⟩ := gotSlots (0x203de0, 0x129770) (by decide)
  obtain ⟨gotRead2, gotVal2⟩ := gotSlots (0x203e20, 0x100a20) (by decide)
  have load (k : Nat) (hk : k < 5) : LoadOk m (wordAddr (q + 88) 64 k) 8 := by
    rw [srcEq]
    have hn : (wordAddr (fr.rsp - 144) 64 k).toNat = fr.rsp.toNat - 144 + 8 * k := by
      simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceDiv, outNat]
      rw [Nat.mod_eq_of_lt (a := 8 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact LoadOk.of_region win.readable (by omega) (by omega)
  have guards :
      StoreOk Extracted.programImage m q 8 0x10ed4c 4 ∧
      StoreOk Extracted.programImage (PackCall.pushed m q w 1 (by decide)) (q + 8) 8 0x10ed50 5 ∧
      StoreOk Extracted.programImage (PackCall.pushed m q w 2 (by decide)) (q + 16) 8 0x10ed55 5 ∧
      StoreOk Extracted.programImage (PackCall.pushed m q w 3 (by decide)) (q + 24) 8 0x10ed5a 5 ∧
      StoreOk Extracted.programImage (PackCall.pushed m q w 4 (by decide)) (q - 8) 8 0x10ed7f 5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp -failIfUnchanged (disch := decide) only [PackCall.pushed, ite_eq_left, ite_eq_right, wordAddr]
      slot_guard using code_l10ed05
  obtain ⟨g0, g1, g2, g3, gp⟩ := guards
  have rspBits : a[4].get 64 = q := congrArg (Value.get 64) rsp
  have inWords : WordsAt m (q + 88) 64 u := srcEq.symm ▸ input
  obtain ⟨b, block, spReg, rcx, rdx, rsi, rdi, r8, keep⟩ :=
    PackCall.packBlock rspBits inWords load g0 g1 g2 g3 gp
  have bwidth (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : b[i].width = 64 := by
    have hk : i.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rw [keep i hk]
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width r3
    · exact congrArg Value.width r5
    · exact congrArg Value.width r12
    · exact congrArg Value.width r13
    · exact congrArg Value.width r14
    · exact congrArg Value.width r15
  have outputWin : Writable Extracted.programImage m₁ (sp + 96) 33 := by
    rw [outEq]
    exact (win.of_frame wf).sub (by omega) (by omega)
  have invWords : WordsAt m₁ (sp + 8) 64 w := by
    rw [argEq]
    exact PackCall.packedStore_words w (subWindow (by decide))
  have coreWin : Writable Extracted.programImage m₁ (sp - 736) 736 := by
    rw [winEq]
    exact (win.of_frame wf).sub (Nat.le_refl _) (by omega)
  obtain ⟨o, run, tag, outSp, outKeep, coreFrame, v, vwords, vval, status⟩ :=
    Invert.coreExecution b m₁ sp z w spReg rcx rdx (argEq.symm ▸ rsi) (by simpa only [outEq, srcEq] using rdi)
      r8 ((keep 22 (by decide)).trans df) bwidth loaded (by omega) (by omega) (by omega)
      gotRead1 gotVal1 gotRead2 gotVal2 (by omega) coreWin
      (packWin.readable.of_frame wf) outputWin (PackCall.packedStore_ret m q w)
      invWords ((PackCall.packed_value u widths).trans zval) nz
  let changes : List MemoryRegion := [⟨(fr.rsp - 976).toNat, 865⟩]
  have prepWithin : RegionsWithin [PackCall.slotRegion q] changes := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (fr.rsp - 976).toNat ≤ sp.toNat ∧ sp.toNat + 40 ≤ (fr.rsp - 976).toNat + 865
    omega
  have allFrame : RamWriteFrame m o.store changes := by
    refine ((RamWriteFrame.refl m changes).trans wf prepWithin).trans coreFrame ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases hr with rfl | rfl <;> simp only [winEq, outEq, winNat, outNat] <;> omega
  have same (k : Word) (hk : k.toNat ≤ 48) :
      memLoad o.store (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply allFrame.memLoad_eq
    simp only [Outside, changes, List.mem_singleton, forall_eq, Nat.reduceDiv,
      sub_toNat stackRoom k (by omega : k.toNat ≤ 976), winNat]
    omega
  have keep' (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      o.values[i] = a[i] := (outKeep i hi).trans (keep i hi)
  have combined : RamWriteFrame fr.original o.store (writes fr) := by
    refine s.frame.trans allFrame ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, .head _, ?_⟩
    change fr.low.toNat ≤ (fr.rsp - 976).toNat ∧
      (fr.rsp - 976).toNat + 865 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega
  refine ⟨o.values, o.store, ?_, ?_, h.of_frame allFrame ?_, ?_⟩
  · let resume := Generate.Generator.callFrame .l10ed84 0x10ed84
    refine .step (b := ⟨⟨.l108e30, b, m₁⟩, [resume]⟩) ?_ ?_
    · simp only [Program.sem, Program.step, block, Transfer.next, resume]
      rfl
    · exact ParseSignature.exec_reaches_resume run resume [] (by rw [tag]; rfl)
  · refine ⟨?_, ?_, s.source.of_frame allFrame, s.dest.of_frame allFrame,
      s.srcAbove, s.dstAbove, combined⟩
    · refine ⟨outSp.trans (congrArg (fun p => (⟨64, p⟩ : Value)) argEq),
        (keep' 22 (by decide)).trans df, (keep' 3 (by decide)).trans r3,
        (keep' 5 (by decide)).trans r5, (keep' 12 (by decide)).trans r12,
        (keep' 13 (by decide)).trans r13, (keep' 14 (by decide)).trans r14,
        (keep' 15 (by decide)).trans r15, (keep' 39 (by decide)).trans r39,
        (keep' 50 (by decide)).trans r50, (keep' 51 (by decide)).trans r51,
        (same 48 (by decide)).trans s48, (same 40 (by decide)).trans s40,
        (same 32 (by decide)).trans s32, (same 24 (by decide)).trans s24,
        (same 16 (by decide)).trans s16, (same 8 (by decide)).trans s8,
        retRead.of_frame allFrame, ?_, retLow, win.of_frame allFrame, room, align, trivial⟩
      have hret := same 0 (by decide)
      rw [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] at hret
      exact hret.trans ret
    · apply scratch_image win _ s.image
      refine (RamWriteFrame.refl _ _).trans allFrame ?_
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (show 865 ≤ 976 by decide) _⟩
  · simp only [Outside, changes, List.mem_singleton, forall_eq, winNat]
    omega
  · exact ⟨v, outEq ▸ vwords, vval, statusEq ▸ status⟩

end K256.Proofs.Signing.Affine
