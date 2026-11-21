import AesGcm.Proofs.AES16.KeySchedule.Entry
import AesGcm.Proofs.Machine.Runtime.Memset
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem entry_zero_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hzero : CallContract LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat])
      (fun fr mem ↦ fr.rsi = 0 ∧ Writable code mem fr.rdi fr.rdx.toNat ∧
        RangeApart fr.rdi fr.rdx.toNat fr.rsp 8)
      (fun fr mem ↦ ∀ i < fr.rdx.toNat, mem[fr.rdi + BitVec.ofNat 64 i]? = some 0))
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hDF : args[22] = ⟨1, 0⟩)
    (hFp39 : args[39] = ⟨32, args[39].get 32⟩)
    (hFp50 : args[50] = ⟨16, args[50].get 16⟩)
    (hFp51 : args[51] = ⟨16, args[51].get 16⟩)
    (hstack : Writable code mem (args[4].get 64 - (if use256 then 608 else 512))
      (if use256 then 608 else 512))
    (hroom : (if use256 then 608 else 512) ≤ (args[4].get 64).toNat)
    (hAlign : (args[4].get 64).toNat % 16 = 8)
    (hslotRead : Readable mem 0x201228 8)
    (hslot : memLoad mem 0x201228 64 = 0x103eb0)
    (hsep : (if use256 then 0x201498 else 0x201438) ≤ (args[4].get 64).toNat ∨
      (args[4].get 64).toNat ≤ 0x201208) :
    ∃ output : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l1057c0 else .l104370), args, mem⟩, []⟩
        ⟨⟨(if use256 then .l1057f1 else .l1043a4), output.values, output.store⟩, []⟩ ∧
      output.values[4].get 64 = args[4].get 64 - (if use256 then 360 else 264) ∧
      output.values[12].get 64 = args[6].get 64 ∧
      output.values[14].get 64 = args[4].get 64 - (if use256 then 348 else 256) ∧
      output.values[15].get 64 = (if use256 then args[15].get 64 else 0) ∧
      output.values[3] = args[3] ∧ output.values[5] = args[5] ∧
      output.values[13] = args[13] ∧ output.values[22] = args[22] ∧
      output.values[39] = args[39] ∧ output.values[50] = args[50] ∧
      output.values[51] = args[51] ∧ GPRsTyped output.values ∧
      RamWriteFrame (entryMemory use256 args mem) output.store
        [span (args[4].get 64 - (if use256 then 368 else 272)) 8,
         span (args[4].get 64 - (if use256 then 348 else 256))
           (if use256 then 240 else 176)] ∧
      (∀ i < (if use256 then 240 else 176),
        output.store[args[4].get 64 - (if use256 then 348 else 256) +
          BitVec.ofNat 64 i]? = some 0) := by
  obtain ⟨callee, cont, hcall, hlabel, htarget, hguard, hmem, h4, h7, h6, h2,
      h12, h14, h15, h3, h5, h13, h22, h39, h50, h51, hCT⟩ :=
    entry_memset_call use256 code hcode args mem hstack hroom hslotRead hslot hsep
  have hcTypes := hCT hTypes
  let av : Values Value Reg.count := callee.arguments
  let ret : BitVec 64 := if use256 then 0x1057f1 else 0x1043a4
  have hfull : Writable code callee.store
      (args[4].get 64 - (if use256 then 608 else 512)) (if use256 then 608 else 512) := by
    rw [hmem]
    exact hstack.of_frame (entryMemory_frame use256 args mem hroom)
  have hRead : Readable callee.store (av[4].get 64) 8 := by
    rw [h4]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hfull ⊢
    all_goals runtime_finish []
  have hRet : memLoad callee.store (av[4].get 64) 64 = ret := by
    rw [h4, hmem]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hRetLow : ret.toNat < 2 ^ 32 := by cases use256 <;> decide
  have hCallAlign : (av[4].get 64).toNat % 16 = 8 := by
    rw [h4]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hroom ⊢
    · have ht : (args[4].get 64 - 272).toNat = (args[4].get 64).toNat - 272 :=
        toNat_sub_ofNat _ 272 (by omega)
      rw [ht]
      omega
    · have ht : (args[4].get 64 - 368).toNat = (args[4].get 64).toNat - 368 :=
        toNat_sub_ofNat _ 368 (by omega)
      rw [ht]
      omega
  have hPre :
      (activationOfValues callee.store av ret (av[4].get 64)).rsi = 0 ∧
      Writable code callee.store (activationOfValues callee.store av ret (av[4].get 64)).rdi
        (activationOfValues callee.store av ret (av[4].get 64)).rdx.toNat ∧
      RangeApart (activationOfValues callee.store av ret (av[4].get 64)).rdi
        (activationOfValues callee.store av ret (av[4].get 64)).rdx.toNat
        (activationOfValues callee.store av ret (av[4].get 64)).rsp 8 := by
    dsimp only [activationOfValues]
    rw [h6, h7, h2, h4]
    refine ⟨rfl, ?_, ?_⟩
    · cases use256 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat] at hfull ⊢
      all_goals runtime_finish []
    · cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat]
      all_goals exact RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  obtain ⟨output, hExec, hTag, hDone, hoTypes, hFrame, hZero⟩ :=
    callContract_exec_values LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat])
      (fun fr m ↦ fr.rsi = 0 ∧ Writable code m fr.rdi fr.rdx.toNat ∧
        RangeApart fr.rdi fr.rdx.toNat fr.rsp 8)
      (fun fr m ↦ ∀ i < fr.rdx.toNat, m[fr.rdi + BitVec.ofNat 64 i]? = some 0)
      hzero callee.store av ret (av[4].get 64) hcTypes
      (by rw [h39, hFp39]; rfl) (by rw [h50, hFp50]; rfl)
      (by rw [h51, hFp51]; rfl) (h22.trans hDF) hRead hRet hRetLow
      (by intro h; change 0 < 0 at h; omega) (by change _ + 0 ≤ _; omega)
      hCallAlign (by trivial) hPre
  change output.values[4] = ⟨64, av[4].get 64 + 8⟩ ∧
    output.values[22] = ⟨1, 0⟩ ∧
    output.values[3] = ⟨64, av[3].get 64⟩ ∧ output.values[5] = ⟨64, av[5].get 64⟩ ∧
    output.values[12] = ⟨64, av[12].get 64⟩ ∧ output.values[13] = ⟨64, av[13].get 64⟩ ∧
    output.values[14] = ⟨64, av[14].get 64⟩ ∧ output.values[15] = ⟨64, av[15].get 64⟩ ∧
    output.values[39] = ⟨32, av[39].get 32⟩ ∧ output.values[50] = ⟨16, av[50].get 16⟩ ∧
    output.values[51] = ⟨16, av[51].get 16⟩ ∧ True at hDone
  rcases hDone with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, _⟩
  have he : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    cases callee with
    | mk label values store => cases hlabel; exact hExec
  have ha : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, hTag, dialect]
    cases use256 <;> rfl
  have hReach := CFGCall.exec_reaches_resume he cont [] ha
  have hv := CFGCall.resume_arguments cont output
  have hl : (cont.resume output).label = (if use256 then .l1057f1 else .l1043a4) := htarget
  have hm : (cont.resume output).store = output.store := rfl
  have hloc : cont.resume output =
      ⟨(if use256 then .l1057f1 else .l1043a4), output.values, output.store⟩ := by
    generalize cont.resume output = loc at hv hl hm ⊢
    cases loc with
    | mk label values store =>
      dsimp only at hv hl hm
      cases hl
      cases hv
      cases hm
      rfl
  rw [hloc] at hReach
  refine ⟨output, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ho22.trans hDF.symm,
    ?_, ?_, ?_, hoTypes, ?_, ?_⟩
  · apply Star.step (b := ⟨callee, [cont]⟩)
    · change (LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1057c0 else .l104370), args, mem⟩).next (dialect code) [] = _
      rw [hcall]
      rfl
    · exact hReach
  · rw [ho4]
    change av[4].get 64 + 8 = _
    rw [h4]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]
    all_goals rfl
  · rw [ho12]
    exact h12
  · rw [ho14]
    exact h14
  · rw [ho15]
    exact h15
  · exact ho3.trans ((hcTypes.value 3).symm.trans h3)
  · exact ho5.trans ((hcTypes.value 5).symm.trans h5)
  · exact ho13.trans ((hcTypes.value 13).symm.trans h13)
  · rw [ho39, h39]
    exact hFp39.symm
  · rw [ho50, h50]
    exact hFp50.symm
  · rw [ho51, h51]
    exact hFp51.symm
  · dsimp only [activationOfValues, Activation.region] at hFrame
    rw [hmem, h4, h7, h2] at hFrame
    cases use256
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat, Nat.sub_self] at hFrame ⊢
    all_goals refine (RamWriteFrame.refl _ _).trans hFrame ?_
    all_goals intro r hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals first
      | exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp [span]⟩
      | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  · dsimp only [activationOfValues] at hZero
    rw [h7, h2] at hZero
    cases use256 <;> simpa only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat] using hZero

end AesGcm.Proofs.Machine.AES16.KeySchedule
