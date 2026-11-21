import AesGcm.Proofs.Machine.Core.Encrypt.Calls
import AesGcm.Proofs.Machine.Core.Interface
import AesGcm.Proofs.AES16.Encrypt
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem mask (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l1029c0 else .l102560))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102980.frameAt .l1029c0 fr else LIR.Fn102520.frameAt .l102560 fr))
    (hTypes : GPRsTyped loc.arguments)
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rsi + 32) loc.store)
    (hr : Readable loc.store fr.rsi (GcmContext.size (AES16.variant use256)))
    (hnonceRead : Readable loc.store fr.rdx 12)
    (hnonce : (span fr.rdx 12).HasBytes loc.store ⟨nonce.toArray⟩)
    (hsrcsep : (callStack fr).Disjoint (span fr.rsi (GcmContext.size (AES16.variant use256))))
    (hnoncesep : (callStack fr).Disjoint (span fr.rdx 12)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102a22 else .l1025c2) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102a22 fr else LIR.Fn102520.frameAt .l1025c2 fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame loc.store next.store
        [span (fr.rsp - BitVec.ofNat 64 (if use256 then 0xb50 else 0x940))
          (if use256 then 0xb50 else 0x940)] ∧
      Fixslice.memoryBlock next.store (fr.rsp - 80) =
        Fixslice16.fromStandard (Standards.NIST.AES.cipher (AES16.variant use256) key
          (nonce ++ #v[(0 : UInt8), 0, 0, 1])) ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 64 = fr.rsi + 32 ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = (loc.arguments[12]'(by change 12 < 53; decide)).get 64 ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 =
        (memLoad loc.store fr.rdx 32).setWidth 64 ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 =
        (memLoad loc.store (fr.rdx + 4) 32).setWidth 64 ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 64 =
        (memLoad loc.store (fr.rdx + 8) 32).setWidth 64 := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hworking hTypes hschedule hr hnonceRead hnonce ⊢
  subst label
  let window : Nat := if use256 then 0xb50 else 0x940
  let aesWindow : Nat := if use256 then 368 else 352
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have facts :
        args[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 200⟩ ∧
        args[22]'(by change 22 < 53; decide) = ⟨1, 0⟩ ∧
        args[1]'(by change 1 < 53; decide) = ⟨64, fr.rcx⟩ ∧
        args[2]'(by change 2 < 53; decide) = ⟨64, fr.rdx⟩ ∧
        args[3]'(by change 3 < 53; decide) = ⟨64, fr.rdi⟩ ∧
        args[5]'(by change 5 < 53; decide) = ⟨64, fr.rbp⟩ ∧
        args[6]'(by change 6 < 53; decide) = ⟨64, fr.rsi⟩ ∧
        args[8]'(by change 8 < 53; decide) = ⟨64, fr.r8⟩ ∧
        args[9]'(by change 9 < 53; decide) = ⟨64, fr.r9⟩ ∧
        args[13]'(by change 13 < 53; decide) = ⟨64, fr.r13⟩ ∧
        args[14]'(by change 14 < 53; decide) = ⟨64, fr.r14⟩ ∧
        args[15]'(by change 15 < 53; decide) = ⟨64, fr.r15⟩ ∧
        args[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ ∧
        args[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ ∧
        args[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ ∧
        memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧
        memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
        memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧
        memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
        memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧
        memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
        Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧
        Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
        fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
        Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
        Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
        Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
        Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
        (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  rcases facts with ⟨h4, h22, h1, h2, h3, h5, h6, h8, h9, h13, h14, h15,
    h39, h50, h51, saved3, saved12, saved13, saved14, saved15, saved5,
    hretRead, hret, hretLow, hstack, hroom, halign,
    hslot0Read, hslot0, hslot1Read, hslot1, hslot2Read, hslot2, hslot3Read, hslot3,
    hslotSep, -⟩
  have h4get : args[4].get 64 = fr.rsp - 200 := by rw [h4]; rfl
  have h2get : args[2].get 64 = fr.rdx := by rw [h2]; rfl
  have h6get : args[6].get 64 = fr.rsi := by rw [h6]; rfl
  have h9get : args[9].get 64 = fr.r9 := by rw [h9]; rfl
  have hwindow : 208 + aesWindow ≤ window := by cases use256 <;> decide
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by
      change n % 2^64 ≤ fr.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := fr.rsp.isLt
      omega)]
  let lower := fr.rsp - BitVec.ofNat 64 window
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hs208 : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := hsub 208 (by omega)
  have hs200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
  have hs184 : (fr.rsp - 184).toNat = fr.rsp.toNat - 184 := hsub 184 (by omega)
  have hs80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := hsub 80 (by omega)
  have hretBound := hretRead.low
  have nonceBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdx.toNat 12 (by omega) (by decide) hnoncesep
  have hw144 : Writable code mem (args[4].get 64 - 8) 144 := by
    rw [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ :=
    mask_runBlock use256 code hcode args mem hw144
      (by simpa only [h2get] using hnonceRead)
      (by rw [h4get, hs200]; omega)
      (by rw [h4get, h2get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega, hs208]; omega)
  have hmemSmall : RamWriteFrame mem callee.store [span (fr.rsp - 208) 144] := by
    rw [hcalleeMem]
    have hf := maskMemory_frame use256 args mem
      (by rw [h4get, hs200]; omega) (by rw [h4get, hs200]; omega)
    simpa only [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega] using hf
  have hmem : RamWriteFrame mem callee.store [span lower window] := by
    apply (RamWriteFrame.refl _ _).trans hmemSmall
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨span lower window, by simp only [List.mem_singleton], ?_, ?_⟩ <;>
      simp only [span, hlower, hs208] <;> omega
  have contextBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat (GcmContext.size (AES16.variant use256)) (by omega)
    (by cases use256 <;> decide) hsrcsep
  have contextOutside : Outside [span lower window] fr.rsi (GcmContext.size (AES16.variant use256)) := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  have scheduleOutside := outside_subregion (offset := 32)
    (count := 16 * ((AES16.variant use256).Nr + 1)) contextOutside
    (by cases use256 <;> decide) (by cases use256 <;> decide)
  have hsched := AES16.scheduleIn_of_frame hschedule hmem scheduleOutside
  have hrSchedule : Readable callee.store (fr.rsi + 32)
      (16 * ((AES16.variant use256).Nr + 1)) := by
    apply (hr.of_frame hmem).of_offsets rfl (addr_self _)
    cases use256 <;> decide +kernel
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 208 := by
    rw [hc4, h4get]
    bv_omega
  have hcallee2 : (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = fr.rsp - 184 := by
    rw [hc2, h4get]
    bv_omega
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = fr.rsp - 80 := by
    rw [hc7, h4get]
    bv_omega
  have hcallee6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = fr.rsi + 32 := by
    rw [hc6, h6get]
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x102a22 else 0x1025c2) lower
  have hafsp : af.rsp = fr.rsp - 208 := hcallee4
  have hafsrc : af.rsi = fr.rsi + 32 := hcallee6
  have hafinput : af.rdx = fr.rsp - 184 := hcallee2
  have hafdst : af.rdi = fr.rsp - 80 := hcallee7
  have haflow : af.low = lower := rfl
  have hAESwindow : (if use256 then LIR.Fn106960.frameInfo else
      LIR.Fn105100.frameInfo).window = aesWindow := by cases use256 <;> rfl
  have hcalleeStack : Writable code callee.store
      ((callee.arguments[4]'(by change 4 < 53; decide)).get 64 - BitVec.ofNat 64 aesWindow)
      aesWindow := by
    rw [hcallee4, BitVec.sub_sub]
    apply (hstack.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have hinput : Fixslice.memoryBlock callee.store (fr.rsp - 184) =
      Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) := by
    have hi := maskMemory_block use256 args mem nonce (by simpa only [h2get] using hnonce)
    rw [h4get, show fr.rsp - 200 + 16 = fr.rsp - 184 by bv_omega] at hi
    simpa only [hcalleeMem] using hi
  have slotOutside (address : BitVec 64) (hlo : 0x201208 ≤ address.toNat)
      (hhi : address.toNat + 8 ≤ 0x201238) : Outside [span lower window] address 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    have hhigh : 0x201238 + window ≤ slotHigh := by cases use256 <;> decide
    simp only [span, hlower]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlots af) := by
    have s1 := (hmem.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hslot1
    have s3 := (hmem.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hslot3
    have hhigh : 0x201238 + aesWindow + 208 ≤ slotHigh := by cases use256 <;> decide
    have sep : 0x201238 + aesWindow ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210 := by
      rw [hafsp, hs208]
      omega
    cases use256 <;> exact ⟨hslot1Read.of_frame hmem, s1, hslot3Read.of_frame hmem, s3, sep, trivial⟩
  have hPre : AES16.ScheduleIn (AES16.variant use256) key af.rsi callee.store ∧
      Readable callee.store af.rsi (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rdx 16 ∧
      Fixslice.memoryBlock callee.store af.rdx =
        Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) ∧
      Writable code callee.store af.rdi 16 ∧
      (callStack af).Disjoint (span af.rdi 16) ∧
      (callStack af).Disjoint (span af.rdx 16) ∧
      (callStack af).Disjoint (span af.rsi (16 * ((AES16.variant use256).Nr + 1))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hafsrc] using hsched
    · simpa only [hafsrc] using hrSchedule
    · rw [hafinput]
      apply (hstack.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    · simpa only [hafinput] using hinput
    · rw [hafdst]
      apply (hstack.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hafdst,
        hlower, hs208, hs80] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hafinput,
        hlower, hs208, hs184] at hx hy
      omega
    · have hsep := outside_disjoint_span scheduleOutside (span lower window) (by simp only [List.mem_singleton])
      intro x hx hy
      apply hsep x (by simpa only [hafsrc, BitVec.ofNat_eq_ofNat] using hy)
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hlower, hs208] at hx ⊢
      omega
  have hc39' := hc39.trans h39
  have hc50' := hc50.trans h50
  have hc51' := hc51.trans h51
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l106960 else .l105100)
      (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo)
      (fun fr ↦ [span fr.rdi 16]) _ _
      (AES16.encrypt_callContract use256 code hcode key (nonce ++ #v[(0 : UInt8), 0, 0, 1]))
      callee.store callee.arguments (if use256 then 0x102a22 else 0x1025c2) lower
      (hcalleeTypes hTypes) (by rw [hc39']; rfl) (by rw [hc50']; rfl) (by rw [hc51']; rfl)
      (hc22.trans h22)
      (by rw [hcallee4]; apply (hstack.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel)
      (by
        rw [hcalleeMem, hc4]
        exact (maskMemory_loads use256 args mem).1)
      (by cases use256 <;> decide)
      (by intro _; cases use256 <;> exact hcalleeStack)
      (by rw [hAESwindow, hcallee4, hlower, hs208]; omega)
      (by rw [hcallee4, hs208]; omega) hslots hPre
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
  have hmemTight : RamWriteFrame mem callee.store [span lower (window - 64)] := by
    apply (RamWriteFrame.refl _ _).trans hmemSmall
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨span lower (window - 64), by simp only [List.mem_singleton], ?_, ?_⟩ <;>
      simp only [span, hlower, hs208] <;> omega
  have calleeWithin : RegionsWithin [af.region, span af.rdi 16] [span lower (window - 64)] := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower (window - 64), by simp only [List.mem_singleton], ?_, ?_⟩ <;>
        simp only [Activation.region, span, haflow, hafsp, hlower, hs208] <;> omega
    · refine ⟨span lower (window - 64), by simp only [List.mem_singleton], ?_, ?_⟩ <;>
        simp only [span, hafdst, hlower, hs80] <;> omega
  have hfTight := hmemTight.trans hframe calleeWithin
  have hf : RamWriteFrame mem output.store [span lower window] := by
    apply (RamWriteFrame.refl _ _).trans hfTight
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    exact ⟨span lower window, by simp only [List.mem_singleton], Nat.le_refl _, by simp only [span]; omega⟩
  have originalSaved (n : Nat) (hn : n ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 n) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 n) 64 := by
    apply hfTight.memLoad_eq
    refine ⟨by rw [hsub n (by omega)]; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower, hsub n (by omega)]
    omega
  have newlySaved (n : Nat) (hn0 : 88 ≤ n) (hn1 : n ≤ 112) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 n) 64 =
        memLoad callee.store (fr.rsp - BitVec.ofNat 64 n) 64 := by
    apply hframe.memLoad_eq
    refine ⟨by rw [hsub n (by omega)]; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region, haflow, hafsp, hlower, hs208, hsub n (by omega)]
      omega
    · simp only [span, hafdst, hs80, hsub n (by omega)]
      omega
  obtain ⟨_, s3, s6, s1, s8, _⟩ := maskMemory_loads use256 args mem
  have new3 : memLoad output.store (fr.rsp - 112) 64 = fr.rdi := by
    have hn := newlySaved 112 (by decide) (by decide)
    calc
      _ = memLoad callee.store (fr.rsp - 112) 64 := by exact hn
      _ = _ := by
        rw [hcalleeMem]
        have hh := s3
        rw [h4get, h3] at hh
        simpa only [Value.get, BitVec.setWidth_eq,
          show fr.rsp - 200 + 88 = fr.rsp - 112 by bv_omega] using hh
  have new6 : memLoad output.store (fr.rsp - 104) 64 = fr.rsi := by
    have hn := newlySaved 104 (by decide) (by decide)
    calc
      _ = memLoad callee.store (fr.rsp - 104) 64 := by exact hn
      _ = _ := by
        rw [hcalleeMem]
        have hh := s6
        rw [h4get, h6] at hh
        simpa only [Value.get, BitVec.setWidth_eq,
          show fr.rsp - 200 + 96 = fr.rsp - 104 by bv_omega] using hh
  have new1 : memLoad output.store (fr.rsp - 96) 64 = fr.rcx := by
    have hn := newlySaved 96 (by decide) (by decide)
    calc
      _ = memLoad callee.store (fr.rsp - 96) 64 := by exact hn
      _ = _ := by
        rw [hcalleeMem]
        have hh := s1
        rw [h4get, h1] at hh
        simpa only [Value.get, BitVec.setWidth_eq,
          show fr.rsp - 200 + 104 = fr.rsp - 96 by bv_omega] using hh
  have new8 : memLoad output.store (fr.rsp - 88) 64 = fr.r8 := by
    have hn := newlySaved 88 (by decide) (by decide)
    calc
      _ = memLoad callee.store (fr.rsp - 88) 64 := by exact hn
      _ = _ := by
        rw [hcalleeMem]
        have hh := s8
        rw [h4get, h8] at hh
        simpa only [Value.get, BitVec.setWidth_eq,
          show fr.rsp - 200 + 112 = fr.rsp - 88 by bv_omega] using hh
  let next := continuation.resume output
  have hnextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have hnextStore : next.store = output.store := rfl
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcalleeLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag]
    cases use256 <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l1029c0 else .l102560), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume, htarget, ?_,
    by simpa only [hnextArgs] using houtTypes, hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnextArgs, hnextStore]
    have outsp : output.values[4] = ⟨64, fr.rsp - 200⟩ := by
      rw [ho4, hafsp, show fr.rsp - 208 + 8 = fr.rsp - 200 by bv_omega]
    have af14 : af.r14 = fr.r9 := hc14.trans h9get
    have af39 : af.mxcsr = fr.mxcsr := congrArg (fun v ↦ v.get 32) hc39'
    have af50 : af.ftw = fr.ftw := congrArg (fun v ↦ v.get 16) hc50'
    have af51 : af.fcw = fr.fcw := congrArg (fun v ↦ v.get 16) hc51'
    have slotEq (a : BitVec 64) (ha0 : 0x201208 ≤ a.toNat) (ha1 : a.toNat + 8 ≤ 0x201238) :
        memLoad output.store a 64 = memLoad mem a 64 := hf.memLoad_eq (slotOutside a ha0 ha1)
    cases use256 <;> exact ⟨outsp, ho22, ho14.trans (congrArg (Value.mk 64) af14),
      ho39.trans (congrArg (Value.mk 32) af39), ho50.trans (congrArg (Value.mk 16) af50),
      ho51.trans (congrArg (Value.mk 16) af51), new3, new6, new1, new8,
      (originalSaved 48 (by decide)).trans saved3, (originalSaved 40 (by decide)).trans saved12,
      (originalSaved 32 (by decide)).trans saved13, (originalSaved 24 (by decide)).trans saved14,
      (originalSaved 16 (by decide)).trans saved15, (originalSaved 8 (by decide)).trans saved5,
      hretRead.of_frame hf, (show memLoad output.store fr.rsp 64 = memLoad mem fr.rsp 64 from by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using originalSaved 0 (by decide)).trans hret, hretLow,
      hstack.of_frame hf, hroom, halign,
      hslot0Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot0,
      hslot1Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot1,
      hslot2Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot2,
      hslot3Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot3,
      hslotSep, trivial⟩
  · simpa only [hnextStore, hafdst] using hpost
  · rw [hnextArgs, ho5]
    exact hc5.trans (congrArg (fun x : BitVec 64 ↦ x + 32) h6get)
  · rw [hnextArgs, ho12]
    exact hc12
  · rw [hnextArgs, ho13]
    exact hc13.trans (congrArg (fun x : BitVec 64 ↦ (memLoad mem x 32).setWidth 64) h2get)
  · rw [hnextArgs, ho15]
    exact hc15.trans (congrArg (fun x : BitVec 64 ↦ (memLoad mem (x + 4) 32).setWidth 64) h2get)
  · rw [hnextArgs, ho3]
    exact hc3.trans (congrArg (fun x : BitVec 64 ↦ (memLoad mem (x + 8) 32).setWidth 64) h2get)

end AesGcm.Proofs.Machine.Core.Encrypt
