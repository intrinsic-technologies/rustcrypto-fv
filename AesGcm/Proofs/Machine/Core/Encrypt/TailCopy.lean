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
theorem copyTailOut (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp destination : BitVec 64) (input : ByteArray)
    (hsp : args[4].get 64 = sp) (hsource : args[13].get 64 = sp + 136)
    (hdestination : args[12].get 64 = destination)
    (hcallee : args[3].get 64 = 0x103f00)
    (hcount : (args[14].get 64).toNat = input.size) (hsize : input.size ≤ 16)
    (hroom : 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 8) 160)
    (hdw : Writable code mem destination input.size)
    (hb : (span (sp + 136) input.size).HasBytes mem input)
    (hsep : (span (sp - 8) 160).Disjoint (span destination input.size))
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102b2e else .l1026ce, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102b3e else .l1026de) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,5,12,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = memLoad mem (sp + 80) 64 ∧
      RamWriteFrame mem next.store [span (sp - 8) 8, span destination input.size] ∧
      (span destination input.size).HasBytes next.store input := by
  have hs8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hroom)
  have hlow : sp.toNat + 152 ≤ 2^32 := by have := hw.readable.low; rw [hs8] at this; omega
  have h136 : (sp + 136).toNat = sp.toNat + 136 := by bv_omega
  have h80 : (sp + 80).toNat = sp.toNat + 80 := by bv_omega
  have hdestLow := hdw.readable.low
  have hr : Readable mem (sp + 136) input.size := by
    apply hw.readable.sub <;> rw [hs8, h136] <;> omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ := copyTailOut_runBlock use256 code hcode args mem
      (by rw [hsp]; exact hw.sub (Nat.le_refl _) (by omega))
      (by rw [hsp]; apply hw.readable.sub <;> rw [hs8, h80] <;> omega) hcallee
  let ret : BitVec 64 := if use256 then 0x102b3e else 0x1026de
  have hmem : RamWriteFrame mem callee.store [span (sp - 8) 8] := by
    rw [hcalleeMem]
    have h := copyTailOutMemory_frame use256 args mem (by rw [hsp]; omega)
    simpa only [hsp] using h
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := hc4.trans (congrArg (fun x : BitVec 64 ↦ x - 8) hsp)
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = destination := hc7.trans hdestination
  have hcallee6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = sp + 136 := hc6.trans hsource
  have hcallee2 : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = input.size := by rw [hc2, hcount]
  let af := activationOfValues callee.store callee.arguments ret (sp - 8)
  have hafsp : af.rsp = sp - 8 := hcallee4
  have haflow : af.low = sp - 8 := rfl
  have hafdst : af.rdi = destination := hcallee7
  have hafsrc : af.rsi = sp + 136 := hcallee6
  have hafcount : af.rdx.toNat = input.size := hcallee2
  have hPre : memcpyPre code af callee.store := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hafsrc, hafcount]; exact hr.of_frame hmem
    · rw [hafdst, hafcount]; exact hdw.of_frame hmem
    · rw [hafsrc, hafdst, hafcount, h136]
      by_cases hp : 0 < input.size
      · have hh := disjoint_bounds (sp - 8).toNat 160 destination.toNat input.size (by decide) hp hsep
        rw [hs8] at hh
        omega
      · omega
    · by_cases hp : 0 < input.size
      · apply RangeApart.of_toNat
        · rw [hafdst, hafcount]; omega
        · rw [hafsp, hs8]; omega
        · rw [hafdst, hafcount, hafsp, hs8]
          have hh := disjoint_bounds (sp - 8).toNat 160 destination.toNat input.size (by decide) hp hsep
          rw [hs8] at hh
          omega
      · intro i hi
        rw [hafcount] at hi
        omega
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
      (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _
      (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
      callee.store callee.arguments ret (sp - 8) (hcalleeTypes hTypes)
      (by rw [hc39, h39]; rfl) (by rw [hc50, h50]; rfl) (by rw [hc51, h51]; rfl)
      (hc22.trans hdf)
      (by rw [hcallee4]; exact (hw.readable.of_frame hmem).sub (Nat.le_refl _) (by omega))
      (by rw [hcallee4, hcalleeMem, copyTailOutMemory, hsp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro h; contradiction)
      (by change (sp - 8).toNat + 0 ≤ _; rw [hcallee4]; omega)
      (by rw [hcallee4, hs8]; omega) (by trivial) hPre
  change Atom.All code output.values output.store (LIR.Fn103f00.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi af.rdx.toNat] at hframe
  change ∀ i < af.rdx.toNat, output.store[af.rdi + BitVec.ofNat 64 i]? =
    callee.store[af.rsi + BitVec.ofNat 64 i]? at hpost
  rcases hdone with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemWide : RamWriteFrame mem callee.store [span (sp - 8) 8, span destination input.size] := by
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
    · exact ⟨span destination input.size, by simp,
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
  have hbytes : (span destination input.size).HasBytes output.store input := by
    refine ⟨rfl, ?_⟩
    intro i
    have he := hpost i.val (by rw [hafcount]; exact i.isLt)
    rw [hafdst, hafsrc] at he
    have ha : destination + BitVec.ofNat 64 i.val = BitVec.ofNat 64 (destination.toNat + i.val) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show i.val < 2^64 by omega)]
    have hb' : (span (sp + 136) input.size).HasBytes callee.store input :=
      hasBytes_of_frame hmem hb (by simp only [span, h136]; omega) (by
        intro r hin x hx hy
        obtain rfl := List.mem_singleton.mp hin
        simp only [span, MemoryRegion.Contains, h136, hs8] at hx hy
        omega)
    rw [ha] at he
    have hs : sp + 136 + BitVec.ofNat 64 i.val = BitVec.ofNat 64 ((sp + 136).toNat + i.val) := by
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
      ⟨⟨(if use256 then .l102b2e else .l1026ce), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans (CFGCall.exec_reaches_resume hexecc continuation [] ha),
    htarget, by simpa only [hnargs] using houtTypes, ?_, ?_, hf, hbytes⟩
  · simpa only [hnargs] using keep
  · rw [hnargs]
    have ho : output.values[13] = ⟨64, af.r13⟩ := ho13
    rw [ho]
    exact hc13.trans (congrArg (fun x : BitVec 64 ↦ memLoad mem (x + 80) 64) hsp)

end AesGcm.Proofs.Machine.Core.Encrypt
