import AesGcm.Proofs.Machine.Core.Encrypt.Calls
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Memset.Unaligned
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.Runtime.MemorySlices

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem zeroTail (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp rem : BitVec 64)
    (hsp : args[4].get 64 = sp) (hrem : args[14].get 64 = rem)
    (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0) (hcount : rem.toNat ≤ 16)
    (hw : Writable code mem (sp - 8) 160)
    (hslotRead : Readable mem 0x201228 8) (hslot : memLoad mem 0x201228 64 = 0x103eb0)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102abe else .l10265e, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102ae3 else .l102683) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      RamWriteFrame mem next.store [span (sp - 8) 8, span (sp + rem + 136) (16 - rem.toNat)] ∧
      (∀ i < 16 - rem.toNat, next.store[sp + rem + 136 + BitVec.ofNat 64 i]? = some 0) := by
  have hs8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have hlow : sp.toNat + 152 ≤ 2^32 := by have := hw.readable.low; rw [hs8] at this; omega
  have hdstNat : (sp + rem + 136).toNat = sp.toNat + rem.toNat + 136 := by bv_omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ := zeroTail_runBlock use256 code hcode args mem
      (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega)) hslotRead hslot
  let ret : BitVec 64 := if use256 then 0x102ae3 else 0x102683
  have hmem : RamWriteFrame mem callee.store [span (sp - 8) 8] := by
    rw [hcalleeMem]
    simpa only [hsp] using zeroTailMemory_frame use256 args mem (by rw [hsp]; exact hroom)
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := hc4.trans (congrArg (fun x : BitVec 64 ↦ x - 8) hsp)
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + rem + 136 := by rw [hc7, hsp, hrem]
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
  have hafdst : af.rdi = sp + rem + 136 := hcallee7
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
      (by rw [hcallee4, hcalleeMem, zeroTailMemory, hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro h; contradiction)
      (by change (sp - 8).toNat + 0 ≤ _; rw [hcallee4]; omega)
      (by rw [hcallee4, hs8]; omega) (by trivial) hPre
  change Atom.All code output.values output.store (LIR.Fn103eb0.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi af.rdx.toNat] at hframe
  change ∀ i < af.rdx.toNat, output.store[af.rdi + BitVec.ofNat 64 i]? = some 0 at hpost
  rcases hdone with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemWide : RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + rem + 136) (16 - rem.toNat)] := by
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
    · exact ⟨span (sp + rem + 136) (16 - rem.toNat), by simp,
        by simp only [span, hafdst]; exact Nat.le_refl _, by simp only [span, hafdst, hafcount]; exact Nat.le_refl _⟩)
  have keep (r : Fin 53) (hr : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho3.trans ((congrArg (Value.mk 64) hc3).trans (hTypes.value 3).symm)
    · change output.values[4] = args[4]
      change output.values[4] = ⟨64, af.rsp + 8⟩ at ho4
      rw [ho4, hafsp, show sp - 8 + 8 = sp by bv_omega]
      exact (congrArg (Value.mk 64) hsp.symm).trans (hTypes.value 4).symm
    · exact ho5.trans ((congrArg (Value.mk 64) hc5).trans (hTypes.value 5).symm)
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
      ⟨⟨(if use256 then .l102abe else .l10265e), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans (CFGCall.exec_reaches_resume hexecc continuation [] ha),
    htarget, by simpa only [hnargs] using houtTypes, ?_, hf, ?_⟩
  · simpa only [hnargs] using keep
  · change ∀ i < 16 - rem.toNat, output.store[sp + rem + 136 + BitVec.ofNat 64 i]? = some 0
    simpa only [hafdst, hafcount] using hpost

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem copyTailIn (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp source : BitVec 64) (input : ByteArray)
    (hsp : args[4].get 64 = sp) (hsource : args[15].get 64 = source)
    (hcount : (args[14].get 64).toNat = input.size) (hsize : input.size ≤ 16)
    (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 8) 160)
    (hr : Readable mem source input.size) (hb : (span source input.size).HasBytes mem input)
    (hsep : (span (sp - 8) 160).Disjoint (span source input.size))
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102ae3 else .l102683, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102b02 else .l1026a2) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,5,12,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 64 = 0x103f00 ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = sp + 136 ∧
      RamWriteFrame mem next.store [span (sp - 8) 8, span (sp + 80) 8, span (sp + 136) input.size] ∧
      memLoad next.store (sp + 80) 64 = args[13].get 64 ∧
      (span (sp + 136) input.size).HasBytes next.store input := by
  have hs8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have hlow : sp.toNat + 152 ≤ 2^32 := by have := hw.readable.low; rw [hs8] at this; omega
  have h136 : (sp + 136).toNat = sp.toNat + 136 := by bv_omega
  have h80 : (sp + 80).toNat = sp.toNat + 80 := by bv_omega
  have hsourceLow := hr.low
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ := copyTailIn_runBlock use256 code hcode args mem
      (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega))
  let ret : BitVec 64 := if use256 then 0x102b02 else 0x1026a2
  have hmem : RamWriteFrame mem callee.store [span (sp - 8) 96] := by
    rw [hcalleeMem]
    have h := copyTailInMemory_frame use256 args mem (by rw [hsp]; omega) (by rw [hsp]; omega)
    simpa only [hsp] using h
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := hc4.trans (congrArg (fun x : BitVec 64 ↦ x - 8) hsp)
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 136 := by rw [hc7, hsp]
  have hcallee6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = source := hc6.trans hsource
  have hcallee2 : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = input.size := by rw [hc2, hcount]
  let af := activationOfValues callee.store callee.arguments ret (sp - 8)
  have hafsp : af.rsp = sp - 8 := hcallee4
  have haflow : af.low = sp - 8 := rfl
  have hafdst : af.rdi = sp + 136 := hcallee7
  have hafsrc : af.rsi = source := hcallee6
  have hafcount : af.rdx.toNat = input.size := hcallee2
  have hPre : memcpyPre code af callee.store := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hafsrc, hafcount]; exact hr.of_frame hmem
    · rw [hafdst, hafcount]
      apply (hw.of_frame hmem).sub <;> rw [hs8, h136] <;> omega
    · rw [hafsrc, hafdst, hafcount, h136]
      by_cases hp : 0 < input.size
      · have hh := disjoint_bounds (sp - 8).toNat 160 source.toNat input.size (by decide) hp hsep
        rw [hs8] at hh
        omega
      · omega
    · apply RangeApart.of_toNat
      all_goals simp only [hafdst, hafcount, hafsp, h136, hs8]
      all_goals omega
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _
      (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
      callee.store callee.arguments ret (sp - 8) (hcalleeTypes hTypes)
      (by rw [hc39, h39]; rfl) (by rw [hc50, h50]; rfl) (by rw [hc51, h51]; rfl)
      (hc22.trans hdf)
      (by rw [hcallee4]; exact (hw.readable.of_frame hmem).sub (Nat.le_refl _) (by omega))
      (by rw [hcallee4, hcalleeMem, copyTailInMemory, hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro h; contradiction)
      (by change (sp - 8).toNat + 0 ≤ _; rw [hcallee4]; omega)
      (by rw [hcallee4, hs8]; omega) (by trivial) hPre
  change Atom.All code output.values output.store (LIR.Fn103f00.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi af.rdx.toNat] at hframe
  change ∀ i < af.rdx.toNat, output.store[af.rdi + BitVec.ofNat 64 i]? =
    callee.store[af.rsi + BitVec.ofNat 64 i]? at hpost
  rcases hdone with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemWide : RamWriteFrame mem callee.store
      [span (sp - 8) 8, span (sp + 80) 8, span (sp + 136) input.size] := by
    rw [hcalleeMem, copyTailInMemory, hsp]
    apply RamWriteFrame.memStore
    · apply (RamWriteFrame.refl _ _).memStore
      refine ⟨span (sp + 80) 8, by simp, ?_⟩
      change (sp + 80).toNat ≤ (sp + 80).toNat ∧
        (sp + 80).toNat + 64 / 8 ≤ (sp + 80).toNat + 8 ∧
        (sp + 80).toNat + 64 / 8 ≤ 2^64
      rw [h80]
      omega
    · refine ⟨span (sp - 8) 8, by simp, ?_⟩
      change (sp - 8).toNat ≤ (sp - 8).toNat ∧
        (sp - 8).toNat + 64 / 8 ≤ (sp - 8).toNat + 8 ∧
        (sp - 8).toNat + 64 / 8 ≤ 2^64
      rw [hs8]
      omega
  have hf := hmemWide.trans hframe (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨span (sp - 8) 8, by simp, by simp only [Activation.region, span, haflow]; exact Nat.le_refl _,
        by simp only [Activation.region, span, haflow, hafsp]; omega⟩
    · exact ⟨span (sp + 136) input.size, by simp,
        by simp only [span, hafdst]; exact Nat.le_refl _, by simp only [span, hafdst, hafcount]; exact Nat.le_refl _⟩)
  have keep (r : Fin 53) (hr : r.val ∈ [4,5,12,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change output.values[4] = args[4]
      change output.values[4] = ⟨64, af.rsp + 8⟩ at ho4
      rw [ho4, hafsp, show sp - 8 + 8 = sp by bv_omega]
      exact (congrArg (Value.mk 64) hsp.symm).trans (hTypes.value 4).symm
    · exact ho5.trans ((congrArg (Value.mk 64) hc5).trans (hTypes.value 5).symm)
    · exact ho12.trans ((congrArg (Value.mk 64) hc12).trans (hTypes.value 12).symm)
    · exact ho14.trans ((congrArg (Value.mk 64) hc14).trans (hTypes.value 14).symm)
    · exact ho15.trans ((congrArg (Value.mk 64) hc15).trans (hTypes.value 15).symm)
    · exact ho22.trans hdf.symm
    · exact ho39.trans ((congrArg (fun x : Value ↦ Value.mk 32 (x.get 32)) hc39).trans h39.symm)
    · exact ho50.trans ((congrArg (fun x : Value ↦ Value.mk 16 (x.get 16)) hc50).trans h50.symm)
    · exact ho51.trans ((congrArg (fun x : Value ↦ Value.mk 16 (x.get 16)) hc51).trans h51.symm)
  have hsave : memLoad output.store (sp + 80) 64 = args[13].get 64 := by
    have he := hframe.memLoad_eq (a := sp + 80) (k := 64) (by
      refine ⟨by rw [h80]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Activation.region, hafsp, haflow, hs8, h80]; omega
      · simp only [span, hafdst, hafcount, h136, h80]; omega)
    rw [he, hcalleeMem, copyTailInMemory, hsp]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_diff; bv_omega),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
  have hbytes : (span (sp + 136) input.size).HasBytes output.store input := by
    refine ⟨rfl, ?_⟩
    intro i
    have he := hpost i.val (by rw [hafcount]; exact i.isLt)
    rw [hafdst, hafsrc] at he
    have ha : sp + 136 + BitVec.ofNat 64 i.val = BitVec.ofNat 64 ((sp + 136).toNat + i.val) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show i.val < 2^64 by omega)]
    have hb' : (span source input.size).HasBytes callee.store input :=
      hasBytes_of_frame hmem hb (by simp only [span]; omega) (by
        intro r hin x hx hy
        obtain rfl := List.mem_singleton.mp hin
        apply hsep x ?_ hx
        simp only [span, MemoryRegion.Contains] at hy ⊢
        omega)
    rw [ha] at he
    have hs : source + BitVec.ofNat 64 i.val = BitVec.ofNat 64 (source.toNat + i.val) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show i.val < 2^64 by omega)]
    exact he.trans (by rw [hs]; exact hb'.2 i)
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
      ⟨⟨(if use256 then .l102ae3 else .l102683), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans (CFGCall.exec_reaches_resume hexecc continuation [] ha),
    htarget, by simpa only [hnargs] using houtTypes, ?_, ?_, ?_, hf, hsave, hbytes⟩
  · simpa only [hnargs] using keep
  · rw [hnargs]
    have ho : output.values[3] = ⟨64, af.rbx⟩ := ho3
    rw [ho]
    exact hc3
  · rw [hnargs]
    have ho : output.values[13] = ⟨64, af.r13⟩ := ho13
    rw [ho]
    exact hc13.trans (congrArg (fun x : BitVec 64 ↦ x + 136) hsp)

end AesGcm.Proofs.Machine.Core.Encrypt
