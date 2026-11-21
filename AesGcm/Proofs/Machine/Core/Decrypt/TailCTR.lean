import AesGcm.Proofs.Machine.Core.Decrypt.Calls
import AesGcm.Proofs.Machine.Core.Decrypt.CTRContract
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.Preservation

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem tailCtrMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (tailCtrMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x10294d else 0x1024ed) ∧
    memLoad (tailCtrMemory use256 args mem) (args[4].get 64 + 16) 64 = args[15].get 64 ∧
    memLoad (tailCtrMemory use256 args mem) (args[4].get 64 + 24) 64 = args[3].get 64 ∧
    memLoad (tailCtrMemory use256 args mem) (args[4].get 64 + 32) 64 = args[3].get 64 ∧
    memLoad (tailCtrMemory use256 args mem) (args[4].get 64 + 40) 64 = 1 := by
  repeat' apply And.intro
  all_goals
    simp only [tailCtrMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          bv_omega)])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem tailCtr_reaches (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (crypt : CTR.CryptCall use256 code key)
    (input : ByteArray) (hsize : input.size = 16)
    (args : Values Value Reg.count) (mem : Ram) (sp schedule : BitVec 64)
    (hsp : args[4].get 64 = sp) (hblock : args[3].get 64 = sp + 152)
    (hcounter : args[15].get 64 = sp + 96)
    (hroom : (if use256 then 0xa80 else 0x870) + 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
      ((if use256 then 0xa80 else 0x870) + 176))
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key schedule mem)
    (hscheduleRead : Readable mem schedule (16 * ((AES16.variant use256).Nr + 1)))
    (hschedulePtr : memLoad mem (sp + 88) 64 = schedule)
    (hbytes : (span (sp + 152) 16).HasBytes mem input)
    (hscheduleSep : (span (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
      ((if use256 then 0xa80 else 0x870) + 176)).Disjoint
      (span schedule (16 * ((AES16.variant use256).Nr + 1))))
    (hslots : Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230)
    (hslotsApart : sp.toNat + 168 ≤ 0x201208 ∨
      0x201238 + (if use256 then 0xa80 else 0x870) + 8 ≤ sp.toNat)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102926 else .l1024c6, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l10294d else .l1024ed) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      RamWriteFrame mem next.store
        [span (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
          ((if use256 then 0xa80 else 0x870) + 64), span (sp + 112) 4, span (sp + 152) 16] ∧
      memLoad next.store (sp + 112) 32 = memLoad mem (sp + 112) 32 + 1 ∧
      (span (sp + 152) 16).HasBytes next.store
        (AesGcm.Spec.GCM.byteArrayOfBits
          (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (sp + 96)))
            (AesGcm.Spec.GCM.bitsOfByteArray input))) := by
  let window : Nat := if use256 then 0xa80 else 0x870
  let lower := sp - BitVec.ofNat 64 (window + 8)
  have hlower : lower.toNat = sp.toNat - (window + 8) := by
    change (sp - BitVec.ofNat 64 (window + 8)).toNat = _
    rw [BitVec.toNat_sub_of_le (by change (window + 8) % 2^64 ≤ sp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := sp.isLt; omega)]
  have hs8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have hlow : sp.toNat + 168 ≤ 2^32 := by
    have hh := hw.readable.low
    change lower.toNat + (window + 176) ≤ 2^32 at hh
    rw [hlower] at hh
    omega
  have hplus (n : Nat) (hn : n ≤ 168) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have localWrite (n count : Nat) (hn : n ≤ 168) (hc : n + count ≤ 168) :
      Writable code mem (sp + BitVec.ofNat 64 n) count := by
    apply hw.sub
    all_goals change _ ≤ _
    all_goals rw [show (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8)).toNat = lower.toNat from rfl,
      hlower, hplus n hn]
    all_goals omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    h4Value, h7Value, h6Value, nativeKeep, hcalleeTypes⟩ := tail_ctr_runBlock use256 code hcode args mem
      (by
        rw [hsp]
        apply hw.sub
        all_goals change _ ≤ _
        all_goals rw [show (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8)).toNat = lower.toNat from rfl,
          hlower, hs8]
        all_goals omega)
  have hc4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = args[4].get 64 - 8 := congrArg (Value.get 64) h4Value
  have hc7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = args[4].get 64 + 88 := congrArg (Value.get 64) h7Value
  have hc6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = args[4].get 64 + 16 := congrArg (Value.get 64) h6Value
  have hc3 : (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[3].get 64 :=
    congrArg (Value.get 64) (nativeKeep 3 (by decide))
  have hc5 : (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 :=
    congrArg (Value.get 64) (nativeKeep 5 (by decide))
  have hc12 : (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 :=
    congrArg (Value.get 64) (nativeKeep 12 (by decide))
  have hc13 : (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 :=
    congrArg (Value.get 64) (nativeKeep 13 (by decide))
  have hc14 : (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 :=
    congrArg (Value.get 64) (nativeKeep 14 (by decide))
  have hc15 : (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 :=
    congrArg (Value.get 64) (nativeKeep 15 (by decide))
  have hc22 : callee.arguments[22]'(by change 22 < 53; decide) = args[22] := nativeKeep 22 (by decide)
  have hc39 : callee.arguments[39]'(by change 39 < 53; decide) = args[39] := nativeKeep 39 (by decide)
  have hc50 : callee.arguments[50]'(by change 50 < 53; decide) = args[50] := nativeKeep 50 (by decide)
  have hc51 : callee.arguments[51]'(by change 51 < 53; decide) = args[51] := nativeKeep 51 (by decide)
  let ret : BitVec 64 := if use256 then 0x10294d else 0x1024ed
  have hmem : RamWriteFrame mem callee.store [span (sp - 8) 56] := by
    rw [hcalleeMem]
    simp only [tailCtrMemory]
    runtime_finish [span,hsp]
  have hloads := tailCtrMemory_loads use256 args mem
  rw [hsp, hblock, hcounter, ← hcalleeMem] at hloads
  have hkey : memLoad callee.store (sp + 88) 64 = schedule := by
    apply Eq.trans (hmem.memLoad_eq _) hschedulePtr
    refine ⟨by have h88 : (sp + 88).toNat = sp.toNat + 88 := hplus 88 (by decide); omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, hs8]
    have h88 : (sp + 88).toNat = sp.toNat + 88 := hplus 88 (by decide)
    omega
  have counterOutside : Outside [span (sp - 8) 56] (sp + 96) 20 := by
    refine ⟨by have h96 : (sp + 96).toNat = sp.toNat + 96 := hplus 96 (by decide); omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, hs8]
    have h96 : (sp + 96).toNat = sp.toNat + 96 := hplus 96 (by decide)
    omega
  have counterLoad (n : Nat) (hn : n ≤ 16) :
      memLoad callee.store ((sp + 96) + BitVec.ofNat 64 n) 32 =
      memLoad mem ((sp + 96) + BitVec.ofNat 64 n) 32 :=
    hmem.memLoad_eq (outside_subregion counterOutside (by omega) (by omega))
  have counterInitial : CTR.initialCounterBlock callee.store (sp + 96) =
      CTR.initialCounterBlock mem (sp + 96) := CTR.initialCounterBlock_of_frame hmem counterOutside
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := hc4.trans (congrArg (fun x : BitVec 64 ↦ x - 8) hsp)
  let af := activationOfValues callee.store callee.arguments ret lower
  have hafsp : af.rsp = sp - 8 := hcallee4
  have haflow : af.low = lower := rfl
  have hafkey : af.rdi = sp + 88 := hc7.trans (congrArg (fun x : BitVec 64 ↦ x + 88) hsp)
  have hafdesc : af.rsi = sp + 16 := hc6.trans (congrArg (fun x : BitVec 64 ↦ x + 16) hsp)
  have localApart (n count m count' : Nat) (hn : n ≤ 168) (hm : m ≤ 168)
      (hap : n + count ≤ m ∨ m + count' ≤ n) :
      (span (sp + BitVec.ofNat 64 n) count).Disjoint (span (sp + BitVec.ofNat 64 m) count') := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hplus n hn, hplus m hm] at hx hy
    omega
  have externalApart (n count : Nat) (hn : n ≤ 168) (hc : n + count ≤ 168) :
      (span (sp + BitVec.ofNat 64 n) count).Disjoint (span schedule (16 * ((AES16.variant use256).Nr + 1))) := by
    intro x hx hy
    apply hscheduleSep x ?_ hy
    change lower.toNat ≤ x ∧ x < lower.toNat + (window + 176)
    simp only [MemoryRegion.Contains, span, hplus n hn] at hx
    rw [hlower]
    omega
  have scheduleOutside : Outside [span (sp - 8) 56] schedule (16 * ((AES16.variant use256).Nr + 1)) := by
    have sep := disjoint_bounds lower.toNat (window + 176) schedule.toNat
      (16 * ((AES16.variant use256).Nr + 1)) (by omega) (by cases use256 <;> decide) hscheduleSep
    refine ⟨by have := hscheduleRead.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, hs8]
    rw [hlower] at sep
    omega
  have preservedBytes := hasBytes_of_frame hmem hbytes (by
    change (sp + 152).toNat + 16 ≤ _
    have h152 : (sp + 152).toNat = sp.toNat + 152 := hplus 152 (by decide)
    omega) (by
      intro r hr x hx hy
      obtain rfl := List.mem_singleton.mp hr
      simp only [span, MemoryRegion.Contains, hs8] at hx hy
      have h152 : (sp + 152).toNat = sp.toNat + 152 := hplus 152 (by decide)
      omega)
  have slotOutside (a : BitVec 64) (ha : 0x201208 ≤ a.toNat) (hb : a.toNat + 8 ≤ 0x201238) :
      Outside [span (sp - 8) 56] a 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, hs8]
    omega
  obtain ⟨s0r, s0v, s1r, s1v, s3r, s3v⟩ := hslots
  have hslotAtoms : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlots af) := by
    have s0 := (hmem.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans s0v
    have s1 := (hmem.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans s1v
    have s3 := (hmem.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans s3v
    have sep : 0x201238 + window ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208 := by rw [hafsp, hs8]; omega
    cases use256 <;> exact ⟨s0r.of_frame hmem, s0, s1r.of_frame hmem, s1, s3r.of_frame hmem, s3, sep, trivial⟩
  have stackApart (n count : Nat) (hn : n ≤ 168) :
      (callStack af).Disjoint (span (sp + BitVec.ofNat 64 n) count) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, callStack, hafsp, haflow, hs8, hplus n hn] at hx hy
    omega
  have hpre :
      Readable callee.store af.rdi 8 ∧ memLoad callee.store af.rdi 64 = schedule ∧
      AES16.ScheduleIn (AES16.variant use256) key schedule callee.store ∧
      Readable callee.store schedule (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rsi 32 ∧ memLoad callee.store af.rsi 64 = sp + 96 ∧
      memLoad callee.store (af.rsi + 8) 64 = sp + 152 ∧
      memLoad callee.store (af.rsi + 16) 64 = sp + 152 ∧
      (memLoad callee.store (af.rsi + 24) 64).toNat = 1 ∧
      Writable code callee.store (sp + 96) 20 ∧ Readable callee.store (sp + 152) input.size ∧
      (span (sp + 152) input.size).HasBytes callee.store input ∧ Writable code callee.store (sp + 152) input.size ∧
      (sp + 152 = sp + 152 ∨ (span (sp + 152) input.size).Disjoint (span (sp + 152) input.size)) ∧
      (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
        (span (sp + 152) input.size).Disjoint (span slot 8) ∧ (span (sp + 96) 20).Disjoint (span slot 8)) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32, span schedule (16 * ((AES16.variant use256).Nr + 1)),
        span (sp + 96) 20, span (sp + 152) input.size, span (sp + 152) input.size], (callStack af).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32, span schedule (16 * ((AES16.variant use256).Nr + 1)), span (sp + 96) 20],
        (span (sp + 152) input.size).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32, span schedule (16 * ((AES16.variant use256).Nr + 1)),
        span (sp + 152) input.size, span (sp + 152) input.size], (span (sp + 96) 20).Disjoint region) := by
    rw [hafkey, hafdesc, hsize]
    refine ⟨(localWrite 88 8 (by decide) (by decide)).readable.of_frame hmem, hkey,
      AES16.scheduleIn_of_frame hschedule hmem scheduleOutside, hscheduleRead.of_frame hmem,
      (localWrite 16 32 (by decide) (by decide)).readable.of_frame hmem, hloads.2.1, ?_, ?_, ?_,
      (localWrite 96 20 (by decide) (by decide)).of_frame hmem,
      (localWrite 152 16 (by decide) (by decide)).readable.of_frame hmem, preservedBytes,
      (localWrite 152 16 (by decide) (by decide)).of_frame hmem, Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · simpa only [show sp + 16 + 8 = sp + 24 by bv_omega] using hloads.2.2.1
    · simpa only [show sp + 16 + 16 = sp + 32 by bv_omega] using hloads.2.2.2.1
    · rw [show sp + 16 + 24 = sp + 40 by bv_omega, hloads.2.2.2.2]; rfl
    · intro slot hs
      have slo : 0x201208 ≤ slot.toNat := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; rcases hs with rfl | rfl | rfl <;> decide
      have shi : slot.toNat + 8 ≤ 0x201238 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; rcases hs with rfl | rfl | rfl <;> decide
      constructor
      all_goals intro x hx hy
      all_goals simp only [span, MemoryRegion.Contains] at hx hy
      all_goals have h152 : (sp + 152).toNat = sp.toNat + 152 := hplus 152 (by decide)
      all_goals have h96 : (sp + 96).toNat = sp.toNat + 96 := hplus 96 (by decide)
      all_goals omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact stackApart 88 8 (by decide)
      · exact stackApart 16 32 (by decide)
      · intro x hx hy
        apply hscheduleSep x ?_ hy
        simp only [callStack, MemoryRegion.Contains, hafsp, haflow, hs8] at hx
        change lower.toNat ≤ x ∧ x < lower.toNat + (window + 176)
        rw [hlower] at hx ⊢
        omega
      · exact stackApart 96 20 (by decide)
      · exact stackApart 152 16 (by decide)
      · exact stackApart 152 16 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact localApart 152 16 88 8 (by decide) (by decide) (by decide)
      · exact localApart 152 16 16 32 (by decide) (by decide) (by decide)
      · exact externalApart 152 16 (by decide) (by decide)
      · exact localApart 152 16 96 20 (by decide) (by decide) (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact localApart 96 20 88 8 (by decide) (by decide) (by decide)
      · exact localApart 96 20 16 32 (by decide) (by decide) (by decide)
      · exact externalApart 96 20 (by decide) (by decide)
      · exact localApart 96 20 152 16 (by decide) (by decide) (by decide)
      · exact localApart 96 20 152 16 (by decide) (by decide) (by decide)
  have hCTRwindow : (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).window = window := by cases use256 <;> rfl
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l1084e0 else .l107050)
      (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo)
      (fun _ ↦ [span ((sp + 96) + 16) 4, span (sp + 152) input.size]) _ _
      (crypt input 1 (by omega) schedule (sp + 96) (sp + 152) (sp + 152))
      callee.store callee.arguments ret lower (hcalleeTypes hTypes)
      (by rw [hc39, h39]; rfl) (by rw [hc50, h50]; rfl) (by rw [hc51, h51]; rfl)
      (hc22.trans hdf)
      (by rw [hcallee4]; apply (hw.readable.of_frame hmem).sub
          all_goals change _ ≤ _
          all_goals rw [show (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8)).toNat = lower.toNat from rfl, hlower, hs8]
          all_goals omega)
      (by rw [hcallee4]; exact hloads.1)
      (by cases use256 <;> decide)
      (by
        intro _
        rw [hCTRwindow, hcallee4]
        have heq : sp - 8 - BitVec.ofNat 64 window = lower := by
          dsimp only [lower]
          rw [BitVec.sub_sub]
          change sp - (BitVec.ofNat 64 8 + BitVec.ofNat 64 window) = _
          rw [← BitVec.ofNat_add, Nat.add_comm 8 window]
        rw [heq]
        exact (hw.of_frame hmem).sub (Nat.le_refl _) (by change lower.toNat + window ≤ lower.toNat + (window + 176); omega))
      (by rw [hCTRwindow, hcallee4, hlower, hs8]; omega)
      (by rw [hcallee4, hs8]; omega) hslotAtoms hpre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span ((sp + 96) + 16) 4, span (sp + 152) input.size] at hframe
  change memLoad output.store ((sp + 96) + 16) 32 = memLoad callee.store ((sp + 96) + 16) 32 + BitVec.ofNat 32 1 ∧ _ at hpost
  have hd : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  rcases hd with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemWide : RamWriteFrame mem callee.store [span lower (window + 64), span (sp + 112) 4, span (sp + 152) 16] := by
    apply (RamWriteFrame.refl _ _).trans hmem
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨span lower (window + 64), by simp, ?_, ?_⟩ <;> simp only [span, hlower, hs8] <;> omega
  have hf := hmemWide.trans hframe (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨span lower (window + 64), by simp, Nat.le_refl _, ?_⟩
      simp only [Activation.region, span, haflow, hafsp, hlower, hs8]
      omega
    · exact ⟨span (sp + 112) 4, by simp,
        by simp only [span, show sp + 96 + 16 = sp + 112 by bv_omega]; exact Nat.le_refl _,
        by simp only [span, show sp + 96 + 16 = sp + 112 by bv_omega]; exact Nat.le_refl _⟩
    · exact ⟨span (sp + 152) 16, by simp, Nat.le_refl _, by simp only [span, hsize]; exact Nat.le_refl _⟩)
  have keep (r : Fin 53) (hr : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho3.trans ((congrArg (Value.mk 64) hc3).trans (hTypes.value 3).symm)
    · change output.values[4] = args[4]
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
      ⟨⟨(if use256 then .l102926 else .l1024c6), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans (CFGCall.exec_reaches_resume hexecc continuation [] ha),
    htarget, by simpa only [hnargs] using houtTypes, ?_, hf, ?_, ?_⟩
  · simpa only [hnargs] using keep
  · have hh := hpost.1
    have he : memLoad callee.store (sp + 96 + 16) 32 = memLoad mem (sp + 96 + 16) 32 := counterLoad 16 (by decide)
    rw [he, show sp + 96 + 16 = sp + 112 by bv_omega] at hh
    exact hh
  · have hp := hpost.2
    change (span (sp + 152) input.size).HasBytes output.store
      (AesGcm.Spec.GCM.byteArrayOfBits (Standards.NIST.GCM.GCTR _
        (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock callee.store (sp + 96))) _)) at hp
    rw [counterInitial] at hp
    have he : span (sp + 152) input.size = span (sp + 152) 16 := congrArg (span (sp + 152)) hsize
    rw [he] at hp
    exact hp

end AesGcm.Proofs.Machine.Core.Decrypt
