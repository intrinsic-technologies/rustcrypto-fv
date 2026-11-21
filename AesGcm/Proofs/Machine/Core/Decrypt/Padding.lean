import AesGcm.Proofs.Machine.Core.Decrypt.Calls
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Memset.Unaligned
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.Runtime.MemorySlices

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem zero_tail_reaches (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp rem : BitVec 64)
    (hsp : args[4].get 64 = sp) (hrem : args[14].get 64 = rem)
    (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0) (hcount : rem.toNat ≤ 16)
    (hw : Writable code mem (sp - 8) 176)
    (hslotRead : Readable mem 0x201228 8) (hslot : memLoad mem 0x201228 64 = 0x103eb0)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l1028e4 else .l102484, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l10290b else .l1024ab) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 8 = args[0].get 8 ∧
      RamWriteFrame mem next.store [span (sp - 8) 8, span (sp + rem + 152) (16 - rem.toNat)] ∧
      (∀ i < 16 - rem.toNat, next.store[sp + rem + 152 + BitVec.ofNat 64 i]? = some 0) := by
  have hs8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have hlow : sp.toNat + 168 ≤ 2^32 := by have := hw.readable.low; rw [hs8] at this; omega
  have hdstNat : (sp + rem + 152).toNat = sp.toNat + rem.toNat + 152 := by bv_omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    c4,c7,c6,c2,c5,nativeKeep,hcalleeTypes⟩ := tail_zero_runBlock use256 code hcode args mem
      (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega)) hslotRead hslot
  have hc4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = args[4].get 64 - 8 := congrArg (Value.get 64) c4
  have hc7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = args[4].get 64 + args[14].get 64 + 152 := congrArg (Value.get 64) c7
  have hc6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = 0 := congrArg (Value.get 64) c6
  have hc2 : (callee.arguments[2]'(by change 2 < 53; decide)).get 64 =
      if args[14].get 64 < 16 then 16 - args[14].get 64 else 0 := congrArg (Value.get 64) c2
  have hc3 : (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[3].get 64 := congrArg (Value.get 64) (nativeKeep 3 (by decide))
  have hc12 : (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 := congrArg (Value.get 64) (nativeKeep 12 (by decide))
  have hc13 : (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 := congrArg (Value.get 64) (nativeKeep 13 (by decide))
  have hc14 : (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 := congrArg (Value.get 64) (nativeKeep 14 (by decide))
  have hc15 : (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 := congrArg (Value.get 64) (nativeKeep 15 (by decide))
  have hc22 : callee.arguments[22]'(by change 22 < 53; decide) = args[22] := nativeKeep 22 (by decide)
  have hc39 : callee.arguments[39]'(by change 39 < 53; decide) = args[39] := nativeKeep 39 (by decide)
  have hc50 : callee.arguments[50]'(by change 50 < 53; decide) = args[50] := nativeKeep 50 (by decide)
  have hc51 : callee.arguments[51]'(by change 51 < 53; decide) = args[51] := nativeKeep 51 (by decide)
  let ret : BitVec 64 := if use256 then 0x10290b else 0x1024ab
  have hmem : RamWriteFrame mem callee.store [span (sp - 8) 8] := by
    rw [hcalleeMem,hsp]
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨span (sp - 8) 8,by simp,?_⟩
    simp only [InRegion,span,hs8]
    omega
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := hc4.trans (congrArg (fun x : BitVec 64 ↦ x - 8) hsp)
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + rem + 152 := by rw [hc7, hsp, hrem]
  have hcallee2 : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = 16 - rem.toNat := by
    rw [hc2, hrem]
    split
    · change ((16 : BitVec 64) - rem).toNat = _
      rw [BitVec.toNat_sub_of_le (by change rem.toNat ≤ 16; exact hcount)]
      rfl
    · have hn : ¬rem.toNat < 16 := ‹¬rem < 16›
      change 0 = _
      omega
  let af := activationOfValues callee.store callee.arguments ret (sp - 8)
  have hafsp : af.rsp = sp - 8 := hcallee4
  have haflow : af.low = sp - 8 := rfl
  have hafdst : af.rdi = sp + rem + 152 := hcallee7
  have hafcount : af.rdx.toNat = 16 - rem.toNat := hcallee2
  have hPre : af.rsi = 0 ∧ Writable code callee.store af.rdi af.rdx.toNat ∧
      RangeApart af.rdi af.rdx.toNat af.rsp 8 := by
    refine ⟨hc6, ?_, ?_⟩
    · rw [hafdst, hafcount]
      apply (hw.of_frame hmem).sub <;> rw [hs8, hdstNat] <;> omega
    · apply RangeApart.of_toNat
      all_goals simp only [hafdst, hafcount, hafsp, hdstNat, hs8]
      all_goals omega
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _ (memset_zero_call_of_writable code hcode)
      callee.store callee.arguments ret (sp - 8) (hcalleeTypes hTypes)
      (by rw [hc39, h39]; rfl) (by rw [hc50, h50]; rfl) (by rw [hc51, h51]; rfl)
      (hc22.trans hdf)
      (by rw [hcallee4]; exact (hw.readable.of_frame hmem).sub (Nat.le_refl _) (by omega))
      (by rw [hcallee4, hcalleeMem, hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro h; contradiction)
      (by change (sp - 8).toNat + 0 ≤ _; rw [hcallee4]; omega)
      (by rw [hcallee4, hs8]; omega) (by trivial) hPre
  change Atom.All code output.values output.store (LIR.Fn103eb0.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi af.rdx.toNat] at hframe
  change ∀ i < af.rdx.toNat, output.store[af.rdi + BitVec.ofNat 64 i]? = some 0 at hpost
  rcases hdone with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemWide : RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + rem + 152) (16 - rem.toNat)] := by
    apply (RamWriteFrame.refl _ _).trans hmem
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨span (sp - 8) 8, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hf := hmemWide.trans hframe (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨span (sp - 8) 8, by simp, by simp only [Activation.region, span, haflow]; exact Nat.le_refl _,
        by simp only [Activation.region, span, haflow, hafsp]; omega⟩
    · exact ⟨span (sp + rem + 152) (16 - rem.toNat), by simp,
        by simp only [span, hafdst]; exact Nat.le_refl _, by simp only [span, hafdst, hafcount]; exact Nat.le_refl _⟩)
  have keep (r : Fin 53) (hr : r.val ∈ [3,4,12,13,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho3.trans ((congrArg (Value.mk 64) hc3).trans (hTypes.value 3).symm)
    · change output.values[4] = args[4]
      change output.values[4] = ⟨64, af.rsp + 8⟩ at ho4
      rw [ho4, hafsp, show sp - 8 + 8 = sp by bv_omega]
      exact (congrArg (Value.mk 64) hsp.symm).trans (hTypes.value 4).symm
    · exact ho12.trans ((congrArg (Value.mk 64) hc12).trans (hTypes.value 12).symm)
    · exact ho13.trans ((congrArg (Value.mk 64) hc13).trans (hTypes.value 13).symm)
    · exact ho14.trans ((congrArg (Value.mk 64) hc14).trans (hTypes.value 14).symm)
    · exact ho15.trans ((congrArg (Value.mk 64) hc15).trans (hTypes.value 15).symm)
    · exact ho22.trans hdf.symm
    · exact ho39.trans ((congrArg (fun x : Value ↦ Value.mk 32 (x.get 32)) hc39).trans h39.symm)
    · exact ho50.trans ((congrArg (fun x : Value ↦ Value.mk 16 (x.get 16)) hc50).trans h50.symm)
    · exact ho51.trans ((congrArg (fun x : Value ↦ Value.mk 16 (x.get 16)) hc51).trans h51.symm)
  let next := continuation.resume output
  have hnargs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcalleeLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag, ret]
    cases use256 <;> rfl
  have hstep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l1028e4 else .l102484), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans (CFGCall.exec_reaches_resume hexecc continuation [] ha),
    htarget, by simpa only [hnargs] using houtTypes, ?_, ?_, hf, ?_⟩
  · simpa only [hnargs] using keep
  · rw [hnargs]
    apply (congrArg (Value.get 8) ho5).trans
    change ((callee.arguments[5]'(by change 5 < 53; decide)).get 64).setWidth 8 = args[0].get 8
    rw [c5]
    simp only [Value.get,BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  · change ∀ i < 16 - rem.toNat, output.store[sp + rem + 152 + BitVec.ofNat 64 i]? = some 0
    simpa only [hafdst, hafcount] using hpost

end AesGcm.Proofs.Machine.Core.Decrypt
