import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance
import AesGcm.Proofs.Machine.CTR.Loop.Output
import AesGcm.Proofs.Machine.CTR.Loop.RoundKey

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

private theorem final_output_resume
    {use256 : Bool} {code : CodeMap} {fr : Activation}
    {args : Values Value Reg.count} {mem : Ram} {sp : BitVec 64}
    {scheduleWords : Vector (BitVec 16) (keyWords use256)}
    {before ca : LIR.lifted.Location} {planes : Planes}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hw : CipherWorkingState use256 code fr args mem sp scheduleWords before)
    (hc : LIR.program.runBlock (dialect code) before = .call ca (batchFinalKeyFrame use256))
    (hl : ca.label = .l10a210)
    (h4 : ca.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩)
    (h7 : ca.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 152⟩)
    (h6 : ca.arguments[6]'(by change 6 < 53; decide) = ⟨64, sp + 8⟩)
    (h2 : ca.arguments[2]'(by change 2 < 53; decide) = ⟨64, 8⟩)
    (hwords : WordsAt ca.store (sp + 8) 64 (Vector.ofFn planes))
    (hkeep : ∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
      ca.arguments[r.val]'r.isLt = before.arguments[r.val]'r.isLt)
    (ht : GPRsTyped ca.arguments)
    (hframe : RamWriteFrame before.store ca.store [span (sp - 8) 8, span (sp + 8) 64])
    (hret : memLoad ca.store (sp - 8) 64 = (if use256 then 0x1087a5 else 0x107315)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨before, []⟩ ⟨next, []⟩ ∧
      next.label = (batchFinalKeyFrame use256).target ∧
      Fixslice.memoryBlocks next.store (sp + 152) = decode planes ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩ ∧
      next.arguments[5]'(by change 5 < 53; decide) = before.arguments[5]'(by change 5 < 53; decide) ∧
      memLoad next.store (sp + 224) 64 = memLoad mem (sp + 224) 64 ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] →
        next.arguments[r.val]'r.isLt = args[r.val]'r.isLt) ∧
      RamWriteFrame mem next.store [span (sp - 296) 512, span (sp + 224) 8] := by
  let ret : BitVec 64 := if use256 then 0x1087a5 else 0x107315
  let child := activationOfValues ca.store ca.arguments ret (sp - 296)
  have lo := hw.stack.readable.low
  have h4' : (ca.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [h4]; rfl
  have h7' : (ca.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 152 := by rw [h7]; rfl
  have h6' : (ca.arguments[6]'(by change 6 < 53; decide)).get 64 = sp + 8 := by rw [h6]; rfl
  have h2' : (ca.arguments[2]'(by change 2 < 53; decide)).get 64 = 8 := by rw [h2]; rfl
  have stack := hw.stack.of_frame hframe
  have hap := hw.slotsApart
  have hsep : 0x2013a0 ≤ sp.toNat ∨ sp.toNat + 232 ≤ 0x201208 := by
    cases use256 <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have keyWrites : RamWriteFrame before.store ca.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl before.store _).trans hframe
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
      simp only [span] <;> bv_omega
  have wide := (native_frame_of_scratch hw keyWrites).1
  have slots : Atom.All code ca.arguments ca.store
      (LIR.Fn10a210.frameInfo.callSlotAtoms LIR.Fn10a210.frameInfo.callSlots child) := by
    change Readable ca.store 0x201210 8 ∧ memLoad ca.store 0x201210 64 = 0x103880 ∧
      Readable ca.store 0x201230 8 ∧ memLoad ca.store 0x201230 64 = 0x101230 ∧
      (0x201238 + 192 ≤ ((ca.arguments[4]'(by change 4 < 53; decide)).get 64).toNat ∨
        ((ca.arguments[4]'(by change 4 < 53; decide)).get 64).toNat ≤ 0x201210) ∧ True
    refine ⟨hw.slot1Readable.of_frame hframe, (wide.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot1Value,
      hw.slot2Readable.of_frame hframe, (wide.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot2Value, ?_, trivial⟩
    rw [h4']
    bv_omega
  have h39 : ca.arguments[39]'(by change 39 < 53; decide) = before.arguments[39]'(by change 39 < 53; decide) := hkeep 39 (by decide)
  have h50 : ca.arguments[50]'(by change 50 < 53; decide) = before.arguments[50]'(by change 50 < 53; decide) := hkeep 50 (by decide)
  have h51 : ca.arguments[51]'(by change 51 < 53; decide) = before.arguments[51]'(by change 51 < 53; decide) := hkeep 51 (by decide)
  have hdf := (hkeep 22 (by decide)).trans hw.df
  obtain ⟨out, he, htRet, hd, htyped, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code .l10a210 LIR.Fn10a210.frameInfo
      (fun f ↦ [span f.rdi 64]) _ _ (AES64.output_call code hcode)
      ca.store ca.arguments ret (sp - 296) ht
      (by rw [h39]; exact hw.x87.1) (by rw [h50]; exact hw.x87.2.1)
      (by rw [h51]; exact hw.x87.2.2) hdf
      (by rw [h4']; apply stack.readable.sub <;> bv_omega)
      (by rw [h4']; exact hret) (by cases use256 <;> decide)
      (fun _ ↦ by rw [h4']; change Writable code ca.store (sp - 8 - 192) 192
                  apply stack.sub <;> bv_omega)
      (by rw [h4']; change (sp - 296).toNat + 192 ≤ (sp - 8).toNat; bv_omega)
      (by rw [h4']; have := hw.aligned; bv_omega) slots (by
        dsimp only [activationOfValues, callStack]
        rw [h2', h4', h6', h7']
        refine ⟨rfl, stack.readable.sub ?_ ?_, stack.sub ?_ ?_, ?_, ?_, ?_⟩
        all_goals first | bv_omega | intro i ha hb
        all_goals simp only [span, MemoryRegion.Contains] at ha hb
        all_goals bv_omega)
  change Fixslice.memoryBlocks out.store ((ca.arguments[7]'(by change 7 < 53; decide)).get 64) =
      decode (fun p ↦ memLoad ca.store (((ca.arguments[6]'(by change 6 < 53; decide)).get 64) + BitVec.ofNat 64 (8 * p.val)) 64) at hp
  rw [h7', h6'] at hp
  have words : (fun p : Fin 8 ↦ memLoad ca.store (sp + 8 + BitVec.ofNat 64 (8 * p.val)) 64) = planes := by
    funext p
    simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn] using hwords p.val p.isLt
  rw [words] at hp
  change out.values[4] = ⟨64, (ca.arguments[4]'(by change 4 < 53; decide)).get 64 + 8⟩ ∧ out.values[22] = ⟨1,0⟩ ∧
    out.values[3] = _ ∧ out.values[5] = ⟨64,(ca.arguments[5]'(by change 5 < 53; decide)).get 64⟩ ∧
    out.values[12] = _ ∧ out.values[13] = _ ∧ out.values[14] = _ ∧ out.values[15] = _ ∧
    out.values[39] = ⟨32,(ca.arguments[39]'(by change 39 < 53; decide)).get 32⟩ ∧ out.values[50] = ⟨16,(ca.arguments[50]'(by change 50 < 53; decide)).get 16⟩ ∧
    out.values[51] = ⟨16,(ca.arguments[51]'(by change 51 < 53; decide)).get 16⟩ ∧ True at hd
  obtain ⟨o4,o22,_,o5,_,_,_,_,o39,o50,o51,_⟩ := hd
  have regs : ∀ r : Fin 53, r.val ∈ [22,39,50,51] → out.values[r.val]'r.isLt = args[r.val]'r.isLt := by
    intro r hr
    apply Eq.trans _ (hw.regFrame r hr)
    rcases r with ⟨r,hr'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact o22.trans hw.df.symm
    · rw [h39] at o39; exact o39.trans hw.x87.1.symm
    · rw [h50] at o50; exact o50.trans hw.x87.2.1.symm
    · rw [h51] at o51; exact o51.trans hw.x87.2.2.symm
  change RamWriteFrame ca.store out.store [child.region, span child.rdi 64] at hf
  dsimp only [child, activationOfValues, Activation.region] at hf
  rw [h4', h7'] at hf
  have small : RamWriteFrame before.store out.store [span (sp - 296) 512] := by
    apply keyWrites.trans hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
      simp only [span] <;> bv_omega
  obtain ⟨hwrite, hcount⟩ := native_frame_of_scratch hw small
  have total := hw.written.trans hwrite (fun r hr ↦ ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have reach := call_contract_resume hc hl he htRet
  refine ⟨_, reach, rfl, hp, ?_, o5.trans ((ht.value 5).symm.trans (hkeep 5 (by decide))),
    hcount.trans hw.countWord, htyped, regs, total⟩
  rw [h4'] at o4
  simpa only [BitVec.sub_add_cancel] using o4

private theorem decode_final_round (u : Bool) (key : Vector UInt8 (AES16.variant u).keyBytes)
    (blocks : Blocks) :
    decode (xorPlanes (Fixslice.subBytes (shiftRows2 (batchRoundState u key blocks
      ((AES16.variant u).Nr - 1)))) (expectedKey (AES16.variant u) key
      ⟨(AES16.variant u).Nr, by omega⟩)) =
      fromStandard (fun b ↦ cipher (AES16.variant u) key (toStandard blocks b)) := by
  let v := AES16.variant u
  let last := encryptRounds (cipherKeys v key) (v.Nr - 1) (toStandard blocks)
  have hplanes : xorPlanes (Fixslice.subBytes (shiftRows2 (phaseEncode (v.Nr - 1) last)))
      (expectedKey v key ⟨v.Nr, by omega⟩) =
      encodeStandard (encryptLast (cipherKeys v key) v.Nr last) := by
    cases u with
    | false => exact encryptLast_expectedKey .aes128 key last
    | true => exact encryptLast_expectedKey .aes256 key last
  change decode (xorPlanes _ _) = _
  rw [show batchRoundState u key blocks ((AES16.variant u).Nr - 1) = phaseEncode (v.Nr - 1) last from rfl,
    hplanes, show encryptLast (cipherKeys v key) v.Nr last = _ from
      encryptRounds_correct v key (toStandard blocks), encodeStandard, decode_encode]

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem batch_cipher_finish
    (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (sp : BitVec 64)
    (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hSchedule : ∀ i : Fin (keyWords use256), scheduleWords[i.val] =
      (narrowScheduleWords (AES16.variant use256) key)[i.val]'(by cases use256 <;> exact i.isLt))
    (count : BitVec 64) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hfinal : CipherFinalState use256 key blocks fr sp loc)
    (hCount : memLoad loc.store (sp + 224) 64 = count) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l1087a5 else .l107315) ∧
      Fixslice.memoryBlocks next.store (sp + 152) =
        Fixslice.fromStandard (fun b =>
          Standards.NIST.AES.cipher (AES16.variant use256) key
            (Fixslice.toStandard blocks b)) ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩ ∧
      next.arguments[5]'(by change 5 < 53; decide) =
        ⟨64, memLoad next.store (sp + 224) 64 <<< 6⟩ ∧
      memLoad next.store (sp + 224) 64 = memLoad mem (sp + 224) 64 ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] →
        next.arguments[r.val]'r.isLt = args[r.val]'r.isLt) ∧
      RamWriteFrame mem next.store
        [span (sp - 296) 512, span (sp + 224) 8] := by
  let v := AES16.variant use256
  let planes := batchRoundState use256 key blocks (v.Nr - 1)
  let lastKey := expectedKey v key ⟨v.Nr, by omega⟩
  have hsp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 = sp := by
    rw [hwork.stackPointer]; rfl
  have hs := hwork.stack.readable.low
  have stack := hwork.stack
  obtain ⟨ca, hcall, hl, h4, h7, h3, h6, h5, hw, hc, hret, hk, ht, hf⟩ :=
    batch_final_rows use256 code hcode loc.arguments loc.store sp count planes
      hwork.typed hsp (stack.sub (by bv_omega) (by bv_omega)) hCount hfinal.regs
  have hcall' : LIR.program.runBlock (dialect code) loc = .call ca (batchFinalRowsFrame use256) := by
    cases loc with
    | mk label a m =>
      have he := hfinal.label
      change label = _ at he
      subst label
      exact hcall
  have hsmall : RamWriteFrame loc.store ca.store [span (sp - 296) 512, span (sp + 224) 8] := by
    apply (RamWriteFrame.refl loc.store _).trans hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [span] <;> bv_omega
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [span] <;> bv_omega
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have hspec : ∀ r : Fin 53, r.val ∈ [22,39,50,51] →
      ca.arguments[r.val]'r.isLt = loc.arguments[r.val]'r.isLt := by
    intro r hr
    apply hk r
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  obtain ⟨mid, hrows, hwMid, hmid, hwords, hpres⟩ :=
    call_advance (kind := 0) hcode hwork hcall' hl ht h4 h7 (fun _ ↦ h6) hspec hret
      (by cases use256 <;> decide) hsmall (hc.trans hCount.symm) hw
  have hm3 : mid.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩ :=
    (hpres 3 (by decide)).trans h3
  have hm5 : mid.arguments[5]'(by change 5 < 53; decide) = ⟨64, count <<< 6⟩ :=
    (hpres 5 (by decide)).trans h5
  let keyOffset : BitVec 64 := if use256 then 1240 else 984
  have hkAddr : sp + 344 + BitVec.ofNat 64 (64 * v.Nr) = sp + keyOffset := by
    cases use256 <;> simp only [v, AES16.variant, keyOffset, Bool.false_eq_true, ↓reduceIte,
      Variant.Nr, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hkeys := round_key_slice use256 mid.store sp key scheduleWords hSchedule
    hwMid.keyRead hwMid.keys ⟨v.Nr, Nat.lt_succ_self _⟩
  change Readable mid.store (sp + 344 + BitVec.ofNat 64 (64 * v.Nr)) 64 ∧
    WordsAt mid.store (sp + 344 + BitVec.ofNat 64 (64 * v.Nr)) 64 (Vector.ofFn lastKey) at hkeys
  rw [hkAddr] at hkeys
  have hms := hwMid.stack.readable.low
  have hsp' : (mid.arguments[4]'(by change 4 < 53; decide)).get 64 = sp := by rw [hwMid.stackPointer]; rfl
  obtain ⟨outCa, hoCall, hoLabel, ho4, ho7, ho6, ho2, hoWords, hoKeep, hoTyped, hoFrame, hoRet⟩ :=
    batch_final_key use256 code hcode mid.arguments mid.store sp
      (Fixslice.subBytes (shiftRows2 planes)) lastKey hwMid.typed hsp' (by rw [hm3]; rfl)
      (hwMid.stack.sub (by bv_omega) (by bv_omega)) hkeys.1
      (by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega) hwords hkeys.2
  have hoCall' : LIR.program.runBlock (dialect code) mid = .call outCa (batchFinalKeyFrame use256) := by
    cases mid with
    | mk label a m =>
      change label = _ at hmid
      subst label
      exact hoCall
  obtain ⟨next, hend, hendLabel, hout, hn4, hn5, hnCount, hnTyped, hnRegs, hnFrame⟩ :=
    final_output_resume hcode hwMid hoCall' hoLabel ho4 ho7 ho6 ho2 hoWords hoKeep hoTyped hoFrame hoRet
  have hnCount' : memLoad next.store (sp + 224) 64 = count :=
    hnCount.trans (hwork.countWord.symm.trans hCount)
  exact ⟨next, hrows.trans hend, hendLabel, hout.trans (decode_final_round use256 key blocks),
    hn4, hn5.trans (hnCount' ▸ hm5), hnCount, hnTyped, hnRegs, hnFrame⟩

end AesGcm.Proofs.Machine.CTR.Loop
