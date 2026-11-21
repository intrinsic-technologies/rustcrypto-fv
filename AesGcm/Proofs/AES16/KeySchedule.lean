import AesGcm.Proofs.AES16.KeySchedule.Prefix
import AesGcm.Proofs.AES16.KeySchedule.FinalCopy
import AesGcm.Proofs.AES16.KeySchedule.Saved
import AesGcm.Proofs.AES16.KeySchedule.Return
import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.Output
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame
import AesGcm.Proofs.AES16.KeySchedule.Zero
import AesGcm.Proofs.Machine.Runtime.Memset.Unaligned
import AesGcm.Proofs.AES16.KeySchedule.Entry
import AesGcm.Proofs.AES16.KeySchedule.Generation

namespace AesGcm.Proofs.Machine.AES16

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem initializer_callContract (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (key : Vector UInt8 (variant use256).keyBytes) :
    CallContract LIR.lifted code (if use256 then .l1057c0 else .l104370)
      (if use256 then LIR.Fn1057c0.frameInfo else LIR.Fn104370.frameInfo)
      (fun fr ↦ [span fr.rdi (16 * ((variant use256).Nr + 1))])
      (fun fr mem ↦ Readable mem fr.rsi (variant use256).keyBytes ∧
        (∀ i : Fin (variant use256).keyBytes,
          mem[fr.rsi + BitVec.ofNat 64 i.val]? = some key[i.val]) ∧
        Writable code mem fr.rdi (16 * ((variant use256).Nr + 1)) ∧
        (callStack fr).Disjoint (span fr.rsi (variant use256).keyBytes) ∧
        (callStack fr).Disjoint (span fr.rdi (16 * ((variant use256).Nr + 1))) ∧
        (span fr.rdi (16 * ((variant use256).Nr + 1))).Disjoint
          (span fr.rsi (variant use256).keyBytes))
      (fun fr mem ↦ ScheduleIn (variant use256) key fr.rdi mem) := by
  dsimp only [CallContract, LIR.lifted]
  intro fr loc hl hm hats hTypes hpre
  rcases loc with ⟨lab, args, mem⟩
  dsimp only at hl hm hats hpre ⊢
  subst lab mem
  change Values Value Reg.count at args
  let sp := fr.rsp - (if use256 then 360 else 264)
  let base := sp + (if use256 then 12 else 8)
  let raw := sp + (if use256 then 288 else 200)
  obtain ⟨startArgs, startMem, hStart, hs4, hsTypes, hsDF, hs14, hs15,
      hsStack, hsRoom, hsAlign, hsReadPanic, hsPanic, hsReadBounds, hsBounds,
      hsApart, hsKeys, hs39, hs50, hs51, hsFrame, hsSaved⟩ :
      ∃ (startArgs : Values Value Reg.count) (startMem : Ram),
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨(if use256 then .l1057c0 else .l104370), args, fr.original⟩, []⟩
          ⟨⟨(if use256 then .l105856 else .l1043d2), startArgs, startMem⟩, []⟩ ∧
        startArgs[4].get 64 = sp ∧ GPRsTyped startArgs ∧ startArgs[22] = ⟨1, 0⟩ ∧
        startArgs[14].get 64 = base ∧ startArgs[15].get 64 = (if use256 then 8 else 0) ∧
        Writable code startMem (sp - 248) (if use256 then 608 else 512) ∧
        248 ≤ sp.toNat ∧ sp.toNat % 16 = 0 ∧
        Readable startMem 0x201210 8 ∧ memLoad startMem 0x201210 64 = 0x103880 ∧
        Readable startMem 0x201230 8 ∧ memLoad startMem 0x201230 64 = 0x101230 ∧
        (0x201330 ≤ sp.toNat ∨ sp.toNat + (if use256 then 360 else 264) ≤ 0x201210) ∧
        KeySchedule.RawSchedulePrefix (variant use256) key ((variant use256).Nk / 4)
          base startMem ∧
        startArgs[39] = ⟨32, fr.mxcsr⟩ ∧ startArgs[50] = ⟨16, fr.ftw⟩ ∧
        startArgs[51] = ⟨16, fr.fcw⟩ ∧
        RamWriteFrame fr.original startMem [fr.region] ∧
        RamWriteFrame (KeySchedule.entryMemory use256 args fr.original) startMem
          [span (sp - 248) 248, span base (if use256 then 240 else 176), span raw 16] := by
    exact initializer_prefix_reaches use256 code hcode key fr args hats hTypes
      ⟨hpre.1, hpre.2.1, hpre.2.2.2.1⟩
  obtain ⟨finalArgs, finalMem, hGenerate, hf4, hf22, hf39, hf50, hf51,
      hfTypes, hfFrame, hfKeys⟩ :=
    KeySchedule.generation_reaches use256 code hcode key startArgs startMem sp
      hs4 hsTypes hsDF (by rw [hs39]; rfl) (by rw [hs50]; rfl)
      (by rw [hs51]; rfl) hs14 hs15 hsStack hsRoom hsAlign
      hsReadPanic hsPanic hsReadBounds hsBounds hsApart hsKeys
  obtain ⟨output, hFinish, hTag, hDone, hTyped, hFrame, hSchedule⟩ :
      ∃ output : Output Value Ram Reg.count,
        LIR.program.Exec (dialect code)
          ⟨⟨(if use256 then .l10593a else .l10446f), finalArgs, finalMem⟩, []⟩ output ∧
        output.tag = some ⟨64, fr.ret⟩ ∧
        Atom.All code output.values output.store
          ((if use256 then LIR.Fn1057c0.frameInfo else LIR.Fn104370.frameInfo).doneAtoms fr) ∧
        GPRsTyped output.values ∧
        RamWriteFrame fr.original output.store
          [fr.region, span fr.rdi (16 * ((variant use256).Nr + 1))] ∧
        ScheduleIn (variant use256) key fr.rdi output.store := by
    have hEntry := KeySchedule.initializer_entry_atoms use256 code fr args hats
    rcases hEntry with ⟨ha4, ha22, ha1, ha2, ha3, ha5, ha6, ha7, ha8, ha9,
      ha12, ha13, ha14, ha15, ha39, ha50, ha51, hRetRead, hRet, hRetLow,
      hStack, hRoom, hAlign, hReadCopy, hCopy, hReadPanic, hPanic,
      hReadZero, hZero, hReadBounds, hBounds, hSep, _⟩
    have hargs4 : args[4].get 64 = fr.rsp := by rw [ha4]; rfl
    have hInitialRoom : (if use256 then 608 else 512) ≤ fr.rsp.toNat := by omega
    have hspNat : sp.toNat = fr.rsp.toNat - (if use256 then 360 else 264) := by
      dsimp only [sp]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    have hsub : (sp - 248).toNat = sp.toNat - 248 := by bv_omega
    have hlim : sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32 := by
      have hh := hsStack.readable.low
      rw [hsub] at hh
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    have hb : base.toNat = sp.toNat + (if use256 then 12 else 8) := by
      dsimp only [base]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    have hbDirect : (sp + (if use256 then 12 else 8)).toNat =
        sp.toNat + (if use256 then 12 else 8) := hb
    have hr : raw.toNat = sp.toNat + (if use256 then 288 else 200) := by
      dsimp only [raw]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    have hSaved : RamWriteFrame (KeySchedule.entryMemory use256 args fr.original) finalMem
        [span (sp - 248) 248, span base (if use256 then 240 else 176), span raw 16] := by
      apply hsSaved.trans hfFrame
      intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl
      · exact ⟨_, List.Mem.head _, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, Nat.le_refl _⟩
    have hFull : RamWriteFrame fr.original finalMem [fr.region] := by
      apply hsFrame.trans hfFrame
      intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl
      all_goals refine ⟨fr.region, List.Mem.head _, ?_, ?_⟩
      all_goals simp only [Activation.region, span, hsub, hbDirect]
      all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    have hbottom : (fr.rsp - (if use256 then 608 else 512)).toNat =
        fr.rsp.toNat - (if use256 then 608 else 512) := by
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    have hBounded : RamWriteFrame fr.original finalMem
        [span (fr.rsp - (if use256 then 608 else 512)) (if use256 then 608 else 512)] := by
      have he := KeySchedule.entryMemory_frame use256 args fr.original
        (by rw [hargs4]; exact hInitialRoom)
      simp only [hargs4] at he
      apply he.trans hSaved
      intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl
      all_goals refine ⟨_, List.Mem.head _, ?_, ?_⟩
      all_goals simp only [span, hbottom, hsub, hb, hr]
      all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    have hCopyOutside : Outside
        [span (fr.rsp - (if use256 then 608 else 512)) (if use256 then 608 else 512)]
        0x201208 8 := by
      refine ⟨by decide, ?_⟩
      intro r hin
      simp only [List.mem_singleton] at hin
      subst r
      simp only [span, hbottom, BitVec.reduceToNat]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    have hStackFinal := hsStack.of_frame hfFrame
    have hCopyStack : Writable code finalMem (sp - 8) (if use256 then 320 else 208) := by
      apply hStackFinal.sub
      all_goals rw [hsub]
      all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    have hSlotApart : RangeApart (sp - 8) (if use256 then 320 else 208) 0x201208 8 := by
      apply RangeApart.of_toNat
      · have hh := hCopyStack.readable.low
        omega
      · decide
      · have hsp8 : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
        rw [hsp8]
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat] at * <;> omega
    obtain ⟨hm3, hm12, hm13, hm14, hm15, hm5, hmDst, hmRet⟩ :=
      KeySchedule.entryMemory_saved use256 args fr.original
    simp only [hargs4] at hm3 hm12 hm13 hm14 hm15 hm5 hmDst hmRet
    have hDstAddress : sp + (if use256 then 304 else 192) =
        fr.rsp - (if use256 then 56 else 72) := by
      dsimp only [sp]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
    have hDstOutside : Outside
        [span (sp - 248) 248, span base (if use256 then 240 else 176), span raw 16]
        (sp + (if use256 then 304 else 192)) 8 := by
      cases use256
      · exact KeySchedule.saved_load_outside false sp hsRoom hlim 192 (by decide) (Or.inr rfl)
      · exact KeySchedule.saved_load_outside true sp hsRoom hlim 304 (by decide) (Or.inr rfl)
    have hDst : memLoad finalMem (sp + (if use256 then 304 else 192)) 64 = fr.rdi := by
      rw [hSaved.memLoad_eq hDstOutside, hDstAddress, hmDst, ha7]
      rfl
    have hOut : Writable code finalMem fr.rdi (if use256 then 240 else 176) := by
      have hh := hpre.2.2.1.of_frame hFull
      cases use256 <;> exact hh
    have hOutApart : fr.rdi.toNat + (if use256 then 240 else 176) ≤ fr.low.toNat ∨
        fr.rsp.toNat + 8 ≤ fr.rdi.toNat := by
      have hh := hpre.2.2.2.2.1 (max fr.low.toNat fr.rdi.toNat)
      simp only [callStack, span, MemoryRegion.Contains] at hh
      cases use256 <;> simp only [variant, Standards.NIST.AES.Variant.Nr,
        Bool.false_eq_true, ↓reduceIte] at * <;> omega
    obtain ⟨copied, hCopyReach, hc4, hc3, hc22, hc39, hc50, hc51, hcTypes,
        hcFrame, hcSchedule⟩ :=
      KeySchedule.adjust_copy_reaches use256 code hcode key finalArgs finalMem sp fr.rdi
        hf4 hfTypes (hf22.trans hsDF) (by rw [hf39, hs39]; rfl)
        (by rw [hf50, hs50]; rfl) (by rw [hf51, hs51]; rfl)
        hCopyStack (by omega) hsAlign hDst (hReadCopy.of_frame hBounded)
        ((hBounded.memLoad_eq hCopyOutside).trans hCopy) hSlotApart hfKeys hOut
        (by have hsp8 : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
            rw [hsp8]
            cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega)
    have hSavedLoad (off : Nat) (hoff : off ≤ 48) :
        memLoad finalMem (fr.rsp - BitVec.ofNat 64 off) 64 =
          memLoad (KeySchedule.entryMemory use256 args fr.original)
            (fr.rsp - BitVec.ofNat 64 off) 64 := by
      have hAddr : sp + BitVec.ofNat 64 ((if use256 then 360 else 264) - off) =
          fr.rsp - BitVec.ofNat 64 off := by
        dsimp only [sp]
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [← hAddr]
      exact hSaved.memLoad_eq (KeySchedule.saved_load_outside use256 sp hsRoom hlim _
        (by omega) (Or.inl (by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)))
    have hReturnLoad (off : Nat) (hoff : off ≤ 48) :
        memLoad copied.store (fr.rsp - BitVec.ofNat 64 off) 64 =
          memLoad finalMem (fr.rsp - BitVec.ofNat 64 off) 64 := by
      have hAddr : sp + BitVec.ofNat 64 ((if use256 then 360 else 264) - off) =
          fr.rsp - BitVec.ofNat 64 off := by
        dsimp only [sp]
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [← hAddr]
      exact hcFrame.memLoad_eq (KeySchedule.return_load_outside use256 sp fr.rdi (by omega) hlim
        (by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega) _
        (by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega) (by omega))
    have hOriginalSaved : Readable fr.original (fr.rsp - 48) 56 := by
      have hSave : Readable fr.original (fr.rsp - 48) 48 := by
        apply hStack.readable.sub
        all_goals rw [hbottom]
        all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
      refine ⟨?_, ?_⟩
      · have hr := hRetRead.low
        have h48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := by bv_omega
        rw [h48]
        omega
      · intro i hi
        by_cases hlt : i < 48
        · exact hSave.present i hlt
        · have haddr : (fr.rsp - 48) + BitVec.ofNat 64 i =
              fr.rsp + BitVec.ofNat 64 (i - 48) := by bv_omega
          rw [haddr]
          exact hRetRead.present (i - 48) (by omega)
    have hReturnRet : memLoad copied.store fr.rsp 64 = fr.ret := by
      have hR := hReturnLoad 0 (by decide)
      have hS := hSavedLoad 0 (by decide)
      simp only [BitVec.sub_zero] at hR hS
      exact hR.trans (hS.trans (hmRet.trans hRet))
    obtain ⟨output, hReturnExec, hReturnMem, hReturnTag, hReturnDone, hReturnTyped⟩ :=
      KeySchedule.return_exec use256 code fr copied.values copied.store
        (by rw [hc4]; dsimp only [sp]; cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega)
        hcTypes (hc22.trans (hf22.trans hsDF))
        (hc39.trans (hf39.trans hs39)) (hc50.trans (hf50.trans hs50))
        (hc51.trans (hf51.trans hs51))
        ((hOriginalSaved.of_frame hFull).of_frame hcFrame) hReturnRet hRetLow
        ((hReturnLoad 48 (by decide)).trans ((hSavedLoad 48 (by decide)).trans
          (hm3.trans (by rw [ha3]; rfl))))
        ((hReturnLoad 40 (by decide)).trans ((hSavedLoad 40 (by decide)).trans
          (hm12.trans (by rw [ha12]; rfl))))
        ((hReturnLoad 32 (by decide)).trans ((hSavedLoad 32 (by decide)).trans
          (hm13.trans (by rw [ha13]; rfl))))
        ((hReturnLoad 24 (by decide)).trans ((hSavedLoad 24 (by decide)).trans
          (hm14.trans (by rw [ha14]; rfl))))
        ((hReturnLoad 16 (by decide)).trans ((hSavedLoad 16 (by decide)).trans
          (hm15.trans (by rw [ha15]; rfl))))
        ((hReturnLoad 8 (by decide)).trans ((hSavedLoad 8 (by decide)).trans
          (hm5.trans (by rw [ha5]; rfl))))
    refine ⟨output, Program.Exec.of_sem (hCopyReach.exec hReturnExec.sem),
      hReturnTag, hReturnDone, hReturnTyped, ?_, ?_⟩
    · rw [hReturnMem]
      have hFull' : RamWriteFrame fr.original finalMem
          [fr.region, span fr.rdi (16 * ((variant use256).Nr + 1))] := by
        apply (RamWriteFrame.refl _ _).trans hFull
        intro r hin
        simp only [List.mem_singleton] at hin
        subst r
        exact ⟨_, List.Mem.head _, Nat.le_refl _, Nat.le_refl _⟩
      apply hFull'.trans hcFrame
      intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl
      · refine ⟨fr.region, List.Mem.head _, ?_, ?_⟩
        all_goals simp only [Activation.region, span]
        all_goals have hsp8 : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
        all_goals rw [hsp8]
        all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
      · refine ⟨fr.region, List.Mem.head _, ?_, ?_⟩
        all_goals change _ ≤ _
        all_goals simp only [Activation.region, span, hbDirect]
        all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
      · refine ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, ?_⟩
        cases use256 <;> exact Nat.le_refl _
    · rw [hReturnMem]
      exact hcSchedule
  refine ⟨output, ?_, hTag, hDone, hTyped, hFrame, hSchedule⟩
  exact Program.Exec.of_sem ((hStart.trans hGenerate).exec hFinish.sem)



end AesGcm.Proofs.Machine.AES16
