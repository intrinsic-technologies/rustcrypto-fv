import AesGcm.Proofs.AES16.KeySchedule.Adjust
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Calls
import AesGcm.Proofs.Machine.Runtime.Memcpy

namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1000000 in
theorem adjust_copy_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (key : Vector UInt8 (variant use256).keyBytes)
    (args : Values Value Reg.count) (mem : Ram) (sp dst : BitVec 64)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hstack : Writable code mem (sp - 8) (if use256 then 320 else 208))
    (hroom : 8 ≤ sp.toNat) (hAlign : sp.toNat % 16 = 0)
    (hdst : memLoad mem (sp + (if use256 then 304 else 192)) 64 = dst)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00)
    (hslotApart : RangeApart (sp - 8) (if use256 then 320 else 208) 0x201208 8)
    (hkeys : RawSchedulePrefix (variant use256) key ((variant use256).Nr + 1)
      (sp + (if use256 then 12 else 8)) mem)
    (hOut : Writable code mem dst (if use256 then 240 else 176))
    (hApart : dst.toNat + (if use256 then 240 else 176) ≤ (sp - 8).toNat ∨
      (sp - 8).toNat + (if use256 then 320 else 208) ≤ dst.toNat) :
    ∃ output : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l10593a else .l10446f), args, mem⟩, []⟩
        ⟨⟨(if use256 then .l10693d else .l1050df), output.values, output.store⟩, []⟩ ∧
      output.values[4].get 64 = sp ∧ output.values[3].get 64 = dst ∧
      output.values[22] = args[22] ∧ output.values[39] = args[39] ∧
      output.values[50] = args[50] ∧ output.values[51] = args[51] ∧
      GPRsTyped output.values ∧
      RamWriteFrame mem output.store
        [span (sp - 8) 8, span (sp + (if use256 then 12 else 8))
          (if use256 then 276 else 184), span dst (if use256 then 240 else 176)] ∧
      ScheduleIn (variant use256) key dst output.store := by
  obtain ⟨callee, cont, hc, hl, ht, hg, hc4, hc7, hc6, hc2, hc3,
      hc22, hc39, hc50, hc51, hcTypes, hcRet, hcFrame, hcWords⟩ :=
    adjust_memcpy_call use256 code hcode args mem sp dst
      (fun r ↦ Fixslice16.encodeStandard (Machine.KeySchedule.roundKeyBlock (variant use256) key r))
      hsp hTypes hstack hroom hdst hslotRead hslot hslotApart
      (fun r p ↦ hkeys r r.isLt p)
  let av : Values Value Reg.count := callee.arguments
  let ret : BitVec 64 := if use256 then 0x10693d else 0x1050df
  have hsLow := hstack.readable.low
  have hdLow := hOut.readable.low
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have hbase : (sp + (if use256 then 12 else 8)).toNat =
      sp.toNat + (if use256 then 12 else 8) := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hcStack := hstack.of_frame hcFrame
  have hcOut := hOut.of_frame hcFrame
  have hRead : Readable callee.store (av[4].get 64) 8 := by
    rw [hc4]
    apply hcStack.readable.sub
    · exact Nat.le_refl _
    · cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hRet : memLoad callee.store (av[4].get 64) 64 = ret := by
    rw [hc4]; exact hcRet
  have hPre : memcpyPre code
      (activationOfValues callee.store av ret (av[4].get 64)) callee.store := by
    dsimp only [memcpyPre, activationOfValues, av]
    rw [hc6, hc7, hc2, hc4]
    have hcount : (if use256 then (240 : BitVec 64) else 176).toNat =
        (if use256 then 240 else 176) := by cases use256 <;> rfl
    rw [hcount]
    refine ⟨?_, hcOut, ?_, ?_⟩
    · apply hcStack.readable.sub
      · rw [hbase, hsub]; omega
      · rw [hbase, hsub]
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · rw [hbase]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    · apply RangeApart.of_toNat
      · have := hcOut.readable.low
        omega
      · have := hRead.low
        rw [hc4] at this
        omega
      · cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have hF39 : av[39] = ⟨32, av[39].get 32⟩ := by rw [hc39, h39]; rfl
  have hF50 : av[50] = ⟨16, av[50].get 16⟩ := by rw [hc50, h50]; rfl
  have hF51 : av[51] = ⟨16, av[51].get 16⟩ := by rw [hc51, h51]; rfl
  obtain ⟨output, hExec, hTag, hDone, hoTypes, hoFrame, hoCopy⟩ :=
    callContract_exec_values LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat]) (memcpyPre code)
      (fun fr m ↦ ∀ i < fr.rdx.toNat,
        m[fr.rdi + BitVec.ofNat 64 i]? = fr.original[fr.rsi + BitVec.ofNat 64 i]?)
      (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
      callee.store av ret (av[4].get 64) hcTypes hF39 hF50 hF51 (hc22.trans hDF)
      hRead hRet (by cases use256 <;> decide)
      (by intro h; change 0 < 0 at h; omega)
      (by change _ + 0 ≤ _; omega)
      (by rw [hc4, hsub]; omega) (by trivial) hPre
  obtain ⟨ho4, hoPreserved⟩ := Generation.Native.pushed_call_done
    LIR.Fn103f00.frameInfo rfl rfl code callee.store av sp ret (av[4].get 64)
    output hc4 hcTypes hF39 hF50 hF51 (hc22.trans hDF) hDone
  have he : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    cases callee with
    | mk label values store => cases hl; exact hExec
  have ha : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hg, hTag, dialect]
    cases use256 <;> rfl
  have hReach := CFGCall.exec_reaches_resume he cont [] ha
  have hv := CFGCall.resume_arguments cont output
  have htarget : (cont.resume output).label = (if use256 then .l10693d else .l1050df) := ht
  have hmem : (cont.resume output).store = output.store := rfl
  have hloc : cont.resume output =
      ⟨(if use256 then .l10693d else .l1050df), output.values, output.store⟩ := by
    generalize cont.resume output = loc at hv htarget hmem ⊢
    cases loc with
    | mk label values store =>
      dsimp only at hv htarget hmem
      cases htarget; cases hv; cases hmem; rfl
  rw [hloc] at hReach
  refine ⟨output, ?_, ?_, ?_, (hoPreserved 22 (by decide)).trans hc22,
    (hoPreserved 39 (by decide)).trans hc39, (hoPreserved 50 (by decide)).trans hc50,
    (hoPreserved 51 (by decide)).trans hc51, hoTypes, ?_, ?_⟩
  · apply Star.step (b := ⟨callee, [cont]⟩)
    · change (LIR.program.runBlock (dialect code) _).next (dialect code) [] = _
      rw [hc]; rfl
    · exact hReach
  · rw [ho4]; rfl
  · exact (congrArg (Value.get 64) (hoPreserved 3 (by decide))).trans hc3
  · have hadj : RamWriteFrame mem callee.store
        [span (sp - 8) 8, span (sp + (if use256 then 12 else 8))
          (if use256 then 276 else 184), span dst (if use256 then 240 else 176)] := by
      apply (RamWriteFrame.refl _ _).trans hcFrame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.Mem.head _, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, Nat.le_refl _⟩
    apply hadj.trans hoFrame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.Mem.head _, ?_, ?_⟩
      all_goals simp only [Activation.region, activationOfValues, av, hc4, span, Nat.sub_self]
      all_goals omega
    · simp only [activationOfValues, av, hc7, hc2]
      refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), Nat.le_refl _, ?_⟩
      cases use256 <;> exact Nat.le_refl _
  · apply scheduleIn_of_copy (src := sp + (if use256 then 12 else 8))
      (before := callee.store)
    · intro r p
      exact (hcWords r p).trans (congrFun (adjustKey_encode (variant use256) key r) p)
    · dsimp only [activationOfValues, av] at hoCopy
      rw [hc7, hc6, hc2] at hoCopy
      cases use256 <;> simpa only [variant, Standards.NIST.AES.Variant.Nr,
        Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat] using hoCopy

end AesGcm.Proofs.Machine.AES16.KeySchedule
