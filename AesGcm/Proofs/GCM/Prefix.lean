import AesGcm.Proofs.GCM.Entry
import AesGcm.Proofs.GCM.Memory
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.AES16.Encrypt
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn102040.Frame
import AesGcm.Proofs.Machine.LIR.Fn102180.Frame

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 400000 in
theorem «prefix» (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l102180 else .l102040))
    (hstore : loc.store = fr.original)
    (hentry : Atom.All code loc.arguments loc.store
      ((if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).entryAtoms fr))
    (hTypes : GPRsTyped loc.arguments)
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key fr.rsi fr.original)
    (hr : Readable fr.original fr.rsi (16 * ((AES16.variant use256).Nr + 1)))
    (hsrcsep : (callStack fr).Disjoint (span fr.rsi (16 * ((AES16.variant use256).Nr + 1)))) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l1021ac else .l10206c) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102180.frameAt .l1021ac fr else LIR.Fn102040.frameAt .l10206c fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame fr.original next.store [fr.region] ∧
      Fixslice.memoryBlock next.store (fr.rsp - 56) =
        Fixslice16.fromStandard (Standards.NIST.AES.cipher (AES16.variant use256) key
          (Vector.replicate 16 0)) := by
  have hAES := AES16.encrypt_callContract use256 code hcode key (Vector.replicate 16 0)
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hstore hentry hTypes ⊢
  subst label mem
  let window : Nat := if use256 then 432 else 416
  let aesWindow : Nat := if use256 then 368 else 352
  let slotHigh : Nat := if use256 then 0x2013e8 else 0x2013d8
  have hwindow : window = aesWindow + 64 := by cases use256 <;> rfl
  have hentry' :
      args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
      args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
      args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
      args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
      args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧
      args[51] = ⟨16, fr.fcw⟩ ∧ Readable fr.original fr.rsp 8 ∧
      memLoad fr.original fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code fr.original (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable fr.original 0x201208 8 ∧ memLoad fr.original 0x201208 64 = 0x103f00 ∧
      Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
      Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hentry
  rcases hentry' with ⟨hsp, hdf, -, -, h3, h5, h6, h7, -, -, h12, h13, h14, h15,
    h39, h50, h51, hretRead, hret, hretLow, hstack, hroom, halign,
    hmemcpyRead, hmemcpy, hslotRead0, hslot0, hslotRead1, hslot1, hslotSep, -⟩
  have hspGet : args[4].get 64 = fr.rsp := by rw [hsp]; rfl
  have h6Get : args[6].get 64 = fr.rsi := by rw [h6]; rfl
  have h7Get : args[7].get 64 = fr.rdi := by rw [h7]; rfl
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by
      change n % 2^64 ≤ fr.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := fr.rsp.isLt
      omega)]
  have hwindowGe : 64 ≤ window := by cases use256 <;> decide
  have hs64 : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 64 hwindowGe
  have hs56 : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 56 (by omega)
  have hs32 : (fr.rsp - 32).toNat = fr.rsp.toNat - 32 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 32 (by omega)
  have hstack64 : Writable code fr.original (fr.rsp - 64) 64 := by
    apply hstack.sub
    · rw [hs64, hsub window (Nat.le_refl _)]
      omega
    · rw [hs64, hsub window (Nat.le_refl _)]
      omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc4, hc7, hc2, hc6, hc3, hc14, hkeep, hcalleeTypes⟩ :=
    entry_encrypt_call use256 code hcode args fr.original
      (by simpa only [hspGet] using hstack64)
  let lower := fr.rsp - BitVec.ofNat 64 window
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hmemWindow : RamWriteFrame fr.original callee.store [span lower window] := by
    rw [hcalleeMem]
    simp only [entryMemory, zeroMemory, savedMemory, hspGet]
    have hin (n : Nat) (hn : n ≤ 64) (hn8 : 8 ≤ n) :
        InRegions [span lower window] (fr.rsp - BitVec.ofNat 64 n) 8 := by
      refine ⟨span lower window, by simp, ?_⟩
      simp only [InRegion, span, hlower, hsub n (by omega)]
      have := hretRead.low
      omega
    exact (((((RamWriteFrame.refl _ _).memStore _ (hin 8 (by decide) (by decide))).memStore _
      (hin 16 (by decide) (by decide))).memStore _ (hin 24 (by decide) (by decide))).memStore _
      (hin 32 (by decide) (by decide))).memStore _ (hin 64 (by decide) (by decide))
  have windowWithin : RegionsWithin [span lower window] [fr.region] := by
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, hlower] <;> omega
  have hmem : RamWriteFrame fr.original callee.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hmemWindow windowWithin
  have srcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat (16 * ((AES16.variant use256).Nr + 1))
    (by omega) (by cases use256 <;> decide) hsrcsep
  have srcOutside : Outside [fr.region] fr.rsi (16 * ((AES16.variant use256).Nr + 1)) := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [Activation.region]
    omega
  have hsched := AES16.scheduleIn_of_frame hschedule hmem srcOutside
  have hsrcRead := hr.of_frame hmem
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 64 := by
    rw [hc4, hspGet]
    rfl
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = fr.rsp - 56 := by
    rw [hc7, hspGet]
    rfl
  have hcallee2 : (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = fr.rsp - 32 := by
    rw [hc2, hspGet]
    rfl
  have hcallee6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = fr.rsi := by
    rw [hc6, h6Get]
  have hcalleeStack : Writable code callee.store
      ((callee.arguments[4]'(by change 4 < 53; decide)).get 64 - BitVec.ofNat 64 aesWindow)
      aesWindow := by
    rw [hcallee4, show fr.rsp - 64 - BitVec.ofNat 64 aesWindow =
      fr.rsp - BitVec.ofNat 64 window by rw [hwindow, BitVec.ofNat_add]; bv_omega]
    apply (hstack.of_frame hmem).sub (Nat.le_refl _)
    omega
  have hreadInput : Readable callee.store (fr.rsp - 32) 16 := by
    apply (hstack64.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have hwriteOutput : Writable code callee.store (fr.rsp - 56) 16 := by
    apply (hstack64.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have hzero : Fixslice.memoryBlock callee.store (fr.rsp - 32) =
      Fixslice16.fromStandard (Vector.replicate 16 0) := by
    apply memoryBlock_zero
    · rw [hcalleeMem]
      simp only [entryMemory, zeroMemory, savedMemory, hspGet]
      runtime_finish []
    · rw [show fr.rsp - 32 + 8 = fr.rsp - 24 by bv_omega, hcalleeMem]
      simp only [entryMemory, zeroMemory, savedMemory, hspGet]
      runtime_finish []
  have hslotBound : 0x201238 + window ≤ slotHigh := by cases use256 <;> decide
  have slotOutside (addr : BitVec 64) (haddr0 : 0x201208 ≤ addr.toNat)
      (haddr1 : addr.toNat + 8 ≤ 0x201238) : Outside [span lower window] addr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x1021ac else 0x10206c) lower
  have hafsp : af.rsp = fr.rsp - 64 := hcallee4
  have haflow : af.low = lower := rfl
  have hafdst : af.rdi = fr.rsp - 56 := hcallee7
  have hafsrc : af.rsi = fr.rsi := hcallee6
  have hafinput : af.rdx = fr.rsp - 32 := hcallee2
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlots af) := by
    have s0 := (hmemWindow.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hslot0
    have s1 := (hmemWindow.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hslot1
    have sep : 0x201238 + aesWindow ≤ (fr.rsp - 64).toNat ∨
        (fr.rsp - 64).toNat ≤ 0x201210 := by rw [hs64]; omega
    cases use256 <;> refine ⟨hslotRead0.of_frame hmemWindow, s0,
      hslotRead1.of_frame hmemWindow, s1, ?_, trivial⟩
    · change 0x201238 + 352 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210
      rw [hafsp]
      exact sep
    · change 0x201238 + 368 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210
      rw [hafsp]
      exact sep
  have hPre : AES16.ScheduleIn (AES16.variant use256) key af.rsi callee.store ∧
      Readable callee.store af.rsi (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rdx 16 ∧
      Fixslice.memoryBlock callee.store af.rdx =
        Fixslice16.fromStandard (Vector.replicate 16 0) ∧
      Writable code callee.store af.rdi 16 ∧
      (callStack af).Disjoint (span af.rdi 16) ∧
      (callStack af).Disjoint (span af.rdx 16) ∧
      (callStack af).Disjoint (span af.rsi (16 * ((AES16.variant use256).Nr + 1))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hafsrc] using hsched
    · simpa only [hafsrc] using hsrcRead
    · simpa only [hafinput] using hreadInput
    · simpa only [hafinput] using hzero
    · simpa only [hafdst] using hwriteOutput
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hafdst,
        hlower, hs64, hs56] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hafinput,
        hlower, hs64, hs32] at hx hy
      omega
    · intro x hx hy
      apply hsrcsep x ?_ (by simpa only [hafsrc] using hy)
      simp only [MemoryRegion.Contains, callStack, hafsp, haflow, hlower, hs64] at hx ⊢
      omega
  have hc39 : (callee.arguments[39]'(by change 39 < 53; decide)) = ⟨32, fr.mxcsr⟩ :=
    (hkeep 39 (by decide)).trans h39
  have hc50 : (callee.arguments[50]'(by change 50 < 53; decide)) = ⟨16, fr.ftw⟩ :=
    (hkeep 50 (by decide)).trans h50
  have hc51 : (callee.arguments[51]'(by change 51 < 53; decide)) = ⟨16, fr.fcw⟩ :=
    (hkeep 51 (by decide)).trans h51
  have hAESwindow : (if use256 then LIR.Fn106960.frameInfo else
      LIR.Fn105100.frameInfo).window = aesWindow := by cases use256 <;> rfl
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l106960 else .l105100)
      (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo)
      (fun fr ↦ [span fr.rdi 16]) _ _ hAES callee.store callee.arguments
      (if use256 then 0x1021ac else 0x10206c) lower (hcalleeTypes hTypes)
      (by rw [hc39]; rfl)
      (by rw [hc50]; rfl)
      (by rw [hc51]; rfl)
      ((hkeep 22 (by decide)).trans hdf)
      (by
        rw [hcallee4]
        exact (hstack64.readable.of_frame hmem).sub (Nat.le_refl _) (by omega))
      (by
        rw [hcallee4, hcalleeMem]
        simp only [entryMemory, hspGet]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro _; cases use256 <;> exact hcalleeStack)
      (by
        rw [hAESwindow, hcallee4, hlower, hs64]
        change fr.rsp.toNat - window + aesWindow ≤ fr.rsp.toNat - 64
        omega)
      (by rw [hcallee4, hs64]; omega) hslots hPre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi 16] at hframe
  change Fixslice.memoryBlock output.store af.rdi = _ at hpost
  have hdone' : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  rcases hdone' with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have calleeWithin : RegionsWithin [af.region, span af.rdi 16] [span lower window] := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
        simp only [Activation.region, span, haflow, hafsp, hlower, hs64] <;> omega
    · refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
        simp only [span, hafdst, hlower, hs56] <;> omega
  have hfWindow : RamWriteFrame fr.original output.store [span lower window] :=
    hmemWindow.trans hframe calleeWithin
  have hf : RamWriteFrame fr.original output.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hfWindow windowWithin
  have savedOutside (n : Nat) (hn : 8 ≤ n) (hn16 : n ≤ 16) :
      Outside [af.region, span af.rdi 16] (fr.rsp - BitVec.ofNat 64 n) 8 := by
    refine ⟨by rw [hsub n (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region, haflow, hafsp, hlower, hs64, hsub n (by omega)]
      omega
    · simp only [span, hafdst, hs56, hsub n (by omega)]
      omega
  have saved3 : memLoad output.store (fr.rsp - 16) 64 = fr.rbx := by
    rw [hframe.memLoad_eq (savedOutside 16 (by decide) (by decide)), hcalleeMem]
    simp only [entryMemory, zeroMemory, savedMemory, hspGet]
    runtime_finish [h3]
  have saved14 : memLoad output.store (fr.rsp - 8) 64 = fr.r14 := by
    rw [hframe.memLoad_eq (savedOutside 8 (by decide) (by decide)), hcalleeMem]
    simp only [entryMemory, zeroMemory, savedMemory, hspGet]
    runtime_finish [h14]
  have outsideRet : Outside [fr.region] fr.rsp 8 := by
    refine ⟨by have := hretRead.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [Activation.region]
    omega
  have houtret : memLoad output.store fr.rsp 64 = fr.ret :=
    (hf.memLoad_eq outsideRet).trans hret
  have houtslot : memLoad output.store 0x201208 64 = 0x103f00 :=
    (hfWindow.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hmemcpy
  have hafbx : af.rbx = fr.rdi := by
    change (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.rdi
    rw [hc3, h7Get]
    rfl
  have haf14 : af.r14 = fr.rsi := by
    change (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = fr.rsi
    rw [hc14, h6Get]
    rfl
  have haf5 : af.rbp = fr.rbp := by
    exact congrArg (fun v ↦ v.get 64) ((hkeep 5 (by decide)).trans h5)
  have haf12 : af.r12 = fr.r12 := by
    exact congrArg (fun v ↦ v.get 64) ((hkeep 12 (by decide)).trans h12)
  have haf13 : af.r13 = fr.r13 := by
    exact congrArg (fun v ↦ v.get 64) ((hkeep 13 (by decide)).trans h13)
  have haf15 : af.r15 = fr.r15 := by
    exact congrArg (fun v ↦ v.get 64) ((hkeep 15 (by decide)).trans h15)
  have haf39 : af.mxcsr = fr.mxcsr := congrArg (fun v ↦ v.get 32) hc39
  have haf50 : af.ftw = fr.ftw := congrArg (fun v ↦ v.get 16) hc50
  have haf51 : af.fcw = fr.fcw := congrArg (fun v ↦ v.get 16) hc51
  let next := continuation.resume output
  have hnextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have hnextStore : next.store = output.store := rfl
  have hnextLabel : next.label = (if use256 then .l1021ac else .l10206c) := htarget
  have hworking : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102180.frameAt .l1021ac fr else LIR.Fn102040.frameAt .l10206c fr) := by
    rw [hnextArgs, hnextStore]
    have hspOut : output.values[4] = ⟨64, fr.rsp - 56⟩ := by
      rw [ho4, hafsp, show fr.rsp - 64 + 8 = fr.rsp - 56 by bv_omega]
    have hslotsOut : (0x201210 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) := by
      have hhigh : 0x201210 + window ≤ slotHigh := by cases use256 <;> decide
      omega
    cases use256 <;> exact ⟨hspOut, ho22, ho3.trans (congrArg (Value.mk 64) hafbx),
      ho5.trans (congrArg (Value.mk 64) haf5), ho12.trans (congrArg (Value.mk 64) haf12),
      ho13.trans (congrArg (Value.mk 64) haf13), ho14.trans (congrArg (Value.mk 64) haf14),
      ho15.trans (congrArg (Value.mk 64) haf15), ho39.trans (congrArg (Value.mk 32) haf39),
      ho50.trans (congrArg (Value.mk 16) haf50), ho51.trans (congrArg (Value.mk 16) haf51),
      saved3, saved14, hretRead.of_frame hf, houtret, hretLow, hstack.of_frame hf,
      hroom, halign, hmemcpyRead.of_frame hf, houtslot, hslotsOut, trivial⟩
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code)
      ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcalleeLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag]
    cases use256 <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l102180 else .l102040), args, fr.original⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume,
    hnextLabel, hworking, ?_, hf, ?_⟩
  · simpa only [hnextArgs] using houtTypes
  · simpa only [hnextStore, hafdst] using hpost
end AesGcm.Proofs.Machine.GCM
