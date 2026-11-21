import AesGcm.Proofs.Machine.Core.Decrypt.MaskMemory
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.AES16.Encrypt
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem mask_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l102759 fr
        else LIR.Fn1022c0.frameAt .l1022f9 fr))
    (hTypes : GPRsTyped args)
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rdi + 32) mem)
    (hscheduleRead : Readable mem (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)))
    (hscheduleSep : (callStack fr).Disjoint
      (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))))
    (hnonceRead : Readable mem fr.rsi 12)
    (hnonce : (span fr.rsi 12).HasBytes mem ⟨nonce.toArray⟩)
    (hnonceSep : (callStack fr).Disjoint (span fr.rsi 12)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l102759 else .l1022f9), args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l1027bc else .l10235c) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt .l1027bc fr
          else LIR.Fn1022c0.frameAt .l10235c fr) ∧
      GPRsTyped next.arguments ∧ RamWriteFrame mem next.store [fr.region] ∧
      next.arguments[3]'(by change 3 < 53; decide) = args[3] ∧ next.arguments[14]'(by change 14 < 53; decide) = args[14] ∧
      Fixslice.memoryBlock next.store (fr.rsp - 96) =
        Fixslice16.fromStandard (Standards.NIST.AES.cipher (AES16.variant use256) key
          (nonce ++ #v[(0 : UInt8), 0, 0, 1])) ∧
      memLoad next.store (fr.rsp - 156) 32 = memLoad mem fr.rsi 32 ∧
      memLoad next.store (fr.rsp - 160) 32 = memLoad mem (fr.rsi + 4) 32 ∧
      memLoad next.store (fr.rsp - 164) 32 = memLoad mem (fr.rsi + 8) 32 ∧
      memLoad next.store (fr.rsp - 144) 64 = fr.rdi + 32 := by
  let window : Nat := if use256 then 2912 else 2384
  let childWindow : Nat := if use256 then 368 else 352
  have hwsize : 224 + childWindow ≤ window := by cases use256 <;> decide
  have hworking' : args[4] = ⟨64, fr.rsp - 216⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[2] = ⟨64, fr.rdx⟩ ∧ args[5] = ⟨64, fr.rcx⟩ ∧
      args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧
      args[8] = ⟨64, fr.r8⟩ ∧ args[9] = ⟨64, fr.r9⟩ ∧
      args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧
      memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧
      memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧
      memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  obtain ⟨h4, h22, h2, h5, h6, h7, h8, h9, h12, h13, h15, h39, h50, h51,
    hs3, hs12, hs13, hs14, hs15, hs5, hretRead, hret, hretLow, hstack, hroom, halign,
    hs0r, hs0, hs1r, hs1, hs2r, hs2, hs3r, hs3slot, hslotsSep, _⟩ := hworking'
  have hsub (off : Nat) (ho : off ≤ window) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have ho64 : off < 2^64 := by have := fr.rsp.isLt; omega
    rw [BitVec.toNat_sub_of_le (by change off % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64]
  have hwin224 : 224 ≤ window := by omega
  have n8 : (fr.rsp - 8).toNat = fr.rsp.toNat - 8 := hsub 8 (by omega)
  have n16 : (fr.rsp - 16).toNat = fr.rsp.toNat - 16 := hsub 16 (by omega)
  have n24 : (fr.rsp - 24).toNat = fr.rsp.toNat - 24 := hsub 24 (by omega)
  have n32 : (fr.rsp - 32).toNat = fr.rsp.toNat - 32 := hsub 32 (by omega)
  have n40 : (fr.rsp - 40).toNat = fr.rsp.toNat - 40 := hsub 40 (by omega)
  have n48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := hsub 48 (by omega)
  have n80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := hsub 80 (by omega)
  have n96 : (fr.rsp - 96).toNat = fr.rsp.toNat - 96 := hsub 96 (by omega)
  have n136 : (fr.rsp - 136).toNat = fr.rsp.toNat - 136 := hsub 136 (by omega)
  have n144 : (fr.rsp - 144).toNat = fr.rsp.toNat - 144 := hsub 144 (by omega)
  have n156 : (fr.rsp - 156).toNat = fr.rsp.toNat - 156 := hsub 156 (by omega)
  have n160 : (fr.rsp - 160).toNat = fr.rsp.toNat - 160 := hsub 160 (by omega)
  have n164 : (fr.rsp - 164).toNat = fr.rsp.toNat - 164 := hsub 164 (by omega)
  have n200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
  have n216 : (fr.rsp - 216).toNat = fr.rsp.toNat - 216 := hsub 216 (by omega)
  have n224 : (fr.rsp - 224).toNat = fr.rsp.toNat - 224 := hsub 224 (by omega)
  have hsp : args[4].get 64 = fr.rsp - 216 := by rw [h4]; rfl
  have hnptr : args[6].get 64 = fr.rsi := by rw [h6]; rfl
  have hctx : args[7].get 64 = fr.rdi := by rw [h7]; rfl
  have he (off : BitVec 64) : args[4].get 64 + off = fr.rsp - (216 - off) := by
    rw [hsp]
    bv_omega
  have he224 : args[4].get 64 - 8 = fr.rsp - 224 := by rw [hsp]; bv_omega
  have hsetup : Writable code mem (args[4].get 64 - 8) 176 := by
    rw [he224]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨callee, cont, hx, hl, hc, hg, hm, c4, c7, c6, c2, c12, c13, c15, keep, typed⟩ :=
    mask_runBlock use256 code hcode args mem hsetup (by rw [hnptr]; exact hnonceRead)
  have hfSetup : RamWriteFrame mem callee.store [span (fr.rsp - 224) 144] := by
    rw [hm, ← he224]
    exact maskMemory_frame use256 args mem
      (by rw [hsp]; have := n216; omega)
      (by rw [hsp]; have := n216; have := hretRead.low; omega)
  have setupWithin : RegionsWithin [span (fr.rsp - 224) 144] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, n224] <;> omega
  have hfSetupFull : RamWriteFrame mem callee.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hfSetup setupWithin
  have dataOutside (ptr : BitVec 64) (n : Nat) (hr : Readable mem ptr n)
      (hn : 0 < n) (hd : (callStack fr).Disjoint (span ptr n)) :
      Outside [span (fr.rsp - 224) 144] ptr n := by
    have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      ptr.toNat n (by omega) hn hd
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, n224]
    omega
  have hschedOut := dataOutside _ _ hscheduleRead
    (by cases use256 <;> decide) hscheduleSep
  have hsched := AES16.scheduleIn_of_frame hschedule hfSetup hschedOut
  have nonceApart : RangeApart (args[4].get 64 + 80) 8 (args[6].get 64 + 8) 4 := by
    rw [he, hnptr]
    apply RangeApart.of_toNat
    · have := hsub 136 (by omega)
      change (fr.rsp - 136).toNat + 8 ≤ 2^64
      have := hretRead.low
      omega
    · have := hnonceRead.low
      bv_omega
    · have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        fr.rsi.toNat 12 (by omega) (by decide) hnonceSep
      have ha : (fr.rsi + 8).toNat = fr.rsi.toNat + 8 := by have := hnonceRead.low; bv_omega
      change (fr.rsp - 136).toNat + 8 ≤ (fr.rsi + 8).toNat ∨
        (fr.rsi + 8).toNat + 4 ≤ (fr.rsp - 136).toNat
      rw [n136, ha]
      omega
  have loads := maskMemory_loads use256 args mem nonceApart
  rw [← hm, hnptr, hctx] at loads
  obtain ⟨w0,w1,w2,w3,l0,l1,l2,lkey,laad,lret⟩ := loads
  have hinput : Fixslice.memoryBlock callee.store (args[4].get 64 + 16) =
      Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) := by
    apply Core.memoryBlock_nonce96_of_words mem callee.store fr.rsi (args[4].get 64 + 16) nonce hnonce
    · rintro ⟨k, hk⟩
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using w0
      · change memLoad callee.store (args[4].get 64 + 16 + 4) 32 = memLoad mem (fr.rsi + 4) 32
        rw [BitVec.add_assoc]
        exact w1
      · change memLoad callee.store (args[4].get 64 + 16 + 8) 32 = memLoad mem (fr.rsi + 8) 32
        rw [BitVec.add_assoc]
        exact w2
    · rw [BitVec.add_assoc]
      exact w3
  let lower := fr.rsp - BitVec.ofNat 64 window
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x1027bc else 0x10235c) lower
  have asp : af.rsp = fr.rsp - 224 := by change (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = _; rw [c4]; exact he224
  have alow : af.low = lower := rfl
  have adst : af.rdi = fr.rsp - 96 := by change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _; rw [c7]; exact he 120
  have asrc : af.rsi = fr.rdi + 32 := by change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _; rw [c6, hctx]; rfl
  have ain : af.rdx = args[4].get 64 + 16 := by change (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = _; rw [c2]; rfl
  have ahigh : lower.toNat = fr.rsp.toNat - window := hsub _ (by omega)
  have childWritable : Writable code callee.store (af.rsp - BitVec.ofNat 64 childWindow) childWindow := by
    rw [asp]
    have haddr : fr.rsp - 224 - BitVec.ofNat 64 childWindow =
        fr.rsp - BitVec.ofNat 64 (224 + childWindow) := by rw [BitVec.ofNat_add]; bv_omega
    rw [haddr]
    apply (hstack.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have readInput : Readable callee.store af.rdx 16 := by
    rw [ain, he]
    apply (hstack.readable.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have writeOutput : Writable code callee.store af.rdi 16 := by
    rw [adst]
    apply (hstack.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have childSep (ptr : BitVec 64) (n : Nat) (hr : Readable mem ptr n)
      (hn : 0 < n) (hd : (callStack fr).Disjoint (span ptr n)) :
      (callStack af).Disjoint (span ptr n) := by
    have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      ptr.toNat n (by omega) hn hd
    intro x hx hy
    simp only [MemoryRegion.Contains, callStack, span, asp, alow, ahigh, n224] at hx hy
    omega
  have slotOut (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238) : Outside [span (fr.rsp - 224) 144] ptr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, n224]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).callSlots af) := by
    have s1 := (hfSetup.memLoad_eq (slotOut _ (by decide) (by decide))).trans hs1
    have s3 := (hfSetup.memLoad_eq (slotOut _ (by decide) (by decide))).trans hs3slot
    have apart : 0x201238 + childWindow ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210 := by
      rw [asp, n224]
      omega
    cases use256 <;> exact ⟨hs1r.of_frame hfSetup, s1, hs3r.of_frame hfSetup, s3, apart, trivial⟩
  have hpre : AES16.ScheduleIn (AES16.variant use256) key af.rsi callee.store ∧
      Readable callee.store af.rsi (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rdx 16 ∧ Fixslice.memoryBlock callee.store af.rdx =
        Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) ∧
      Writable code callee.store af.rdi 16 ∧
      (callStack af).Disjoint (span af.rdi 16) ∧
      (callStack af).Disjoint (span af.rdx 16) ∧
      (callStack af).Disjoint (span af.rsi (16 * ((AES16.variant use256).Nr + 1))) := by
    refine ⟨by rw [asrc]; exact hsched, by rw [asrc]; exact hscheduleRead.of_frame hfSetup,
      readInput, by rw [ain]; exact hinput, writeOutput, ?_, ?_, ?_⟩
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, adst, ahigh,
        n224, n96] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, ain, he, ahigh,
        n224] at hx hy
      change (fr.rsp - 200).toNat ≤ x ∧ x < (fr.rsp - 200).toNat + 16 at hy
      rw [n200] at hy
      omega
    · rw [asrc]
      exact childSep _ _ hscheduleRead (by cases use256 <;> decide) hscheduleSep
  have cw : (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).window = childWindow := by
    cases use256 <;> rfl
  have c39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ :=
    (keep 39 (by decide)).trans h39
  have c50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ :=
    (keep 50 (by decide)).trans h50
  have c51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ :=
    (keep 51 (by decide)).trans h51
  obtain ⟨output, hexec, htag, hdone, ht, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l106960 else .l105100)
      (if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo)
      (fun fr ↦ [span fr.rdi 16]) _ _
      (AES16.encrypt_callContract use256 code hcode key (nonce ++ #v[(0 : UInt8), 0, 0, 1]))
      callee.store callee.arguments (if use256 then 0x1027bc else 0x10235c) lower
      (typed hTypes) (by rw [c39]; rfl) (by rw [c50]; rfl) (by rw [c51]; rfl)
      ((keep 22 (by decide)).trans h22)
      (by change Readable callee.store af.rsp 8; rw [asp, ← he224]; exact hsetup.readable.of_frame hfSetup |>.of_offsets (addr_self _) (addr_self _) (by decide))
      (by change memLoad callee.store af.rsp 64 = _; rw [asp, ← he224]; exact lret)
      (by cases use256 <;> decide)
      (by intro _; rw [cw]; exact childWritable)
      (by change lower.toNat + _ ≤ af.rsp.toNat; rw [cw, asp, ahigh, n224]; omega)
      (by change af.rsp.toNat % 16 = 8; rw [asp, n224]; omega)
      hslots hpre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi 16] at hf
  change Fixslice.memoryBlock output.store af.rdi = _ at hp
  let writes := [span lower (window - 48)]
  have setupWithinWrites : RegionsWithin [span (fr.rsp - 224) 144] writes := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨span lower (window - 48), by simp [writes], ?_, ?_⟩ <;>
      simp only [span, ahigh, n224] <;> omega
  have childWithinWrites : RegionsWithin [af.region, span af.rdi 16] writes := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨span lower (window - 48), by simp [writes], ?_, ?_⟩ <;>
        simp only [Activation.region, alow, asp, span, ahigh, n224] <;> omega
    · refine ⟨span lower (window - 48), by simp [writes], ?_, ?_⟩ <;>
        simp only [adst, span, ahigh, n96] <;> omega
  have hfWork : RamWriteFrame mem output.store writes :=
    ((RamWriteFrame.refl _ _).trans hfSetup setupWithinWrites).trans hf childWithinWrites
  have hfFull : RamWriteFrame mem output.store [fr.region] := by
    apply (RamWriteFrame.refl _ _).trans hfWork
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, ahigh] <;> omega
  have savedLoad (off : Nat) (ho : off ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
    apply hfWork.memLoad_eq
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, ahigh, hsub off (by omega)]
    omega
  have childLoad (off bits : Nat) (hoff : 96 + bits / 8 ≤ off) (ho : off ≤ 216)
      (hb : bits / 8 ≤ 8) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 off) bits =
        memLoad callee.store (fr.rsp - BitVec.ofNat 64 off) bits := by
    apply hf.memLoad_eq
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Activation.region, alow, asp, ahigh, n224, hsub off (by omega)]
      omega
    · simp only [span, adst, n96, hsub off (by omega)]
      omega
  have saved3 : memLoad output.store (fr.rsp - 48) 64 = fr.rbx :=
    (savedLoad 48 (by decide)).trans hs3
  have saved12 : memLoad output.store (fr.rsp - 40) 64 = fr.r12 :=
    (savedLoad 40 (by decide)).trans hs12
  have saved13 : memLoad output.store (fr.rsp - 32) 64 = fr.r13 :=
    (savedLoad 32 (by decide)).trans hs13
  have saved14 : memLoad output.store (fr.rsp - 24) 64 = fr.r14 :=
    (savedLoad 24 (by decide)).trans hs14
  have saved15 : memLoad output.store (fr.rsp - 16) 64 = fr.r15 :=
    (savedLoad 16 (by decide)).trans hs15
  have saved5 : memLoad output.store (fr.rsp - 8) 64 = fr.rbp :=
    (savedLoad 8 (by decide)).trans hs5
  have savedReturn : memLoad output.store fr.rsp 64 = fr.ret := by
    have h := savedLoad 0 (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans hret
  have aadLocal : memLoad callee.store (fr.rsp - 136) 64 = fr.rdx := by
    rw [he] at laad
    rw [h2] at laad
    exact laad
  have aadOut : memLoad output.store (fr.rsp - 136) 64 = fr.rdx :=
    (childLoad 136 64 (by decide) (by decide) (by decide)).trans aadLocal
  have outSlot (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238) : memLoad output.store ptr 64 = memLoad mem ptr 64 := by
    apply hfWork.memLoad_eq
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, ahigh]
    omega
  have ho : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  obtain ⟨o4,o22,o3,o5,o12,o13,o14,o15,o39,o50,o51,_⟩ := ho
  have o4' : output.values[4] = ⟨64, fr.rsp - 216⟩ := by
    rw [o4, asp]
    congr 1
    bv_omega
  have af3 : af.rbx = args[3].get 64 := congrArg (Value.get 64) (keep 3 (by decide))
  have af5 : af.rbp = fr.rcx := by
    change (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = _
    exact congrArg (Value.get 64) ((keep 5 (by decide)).trans h5)
  have af12 : af.r12 = fr.rdi := by
    change (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = _
    rw [c12, hctx]
    rfl
  have af13 : af.r13 = fr.r9 := by
    change (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = _
    rw [c13, h9]
    rfl
  have af14 : af.r14 = args[14].get 64 := congrArg (Value.get 64) (keep 14 (by decide))
  have af15 : af.r15 = fr.r8 := by
    change (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = _
    rw [c15, h8]
    rfl
  have af39 : af.mxcsr = fr.mxcsr := congrArg (Value.get 32) c39
  have af50 : af.ftw = fr.ftw := congrArg (Value.get 16) c50
  have af51 : af.fcw = fr.fcw := congrArg (Value.get 16) c51
  have o3' : output.values[3] = args[3] := by
    rw [o3, af3]
    exact (hTypes.value 3).symm
  have o14' : output.values[14] = args[14] := by
    rw [o14, af14]
    exact (hTypes.value 14).symm
  let next := cont.resume output
  have na : next.arguments = output.values := CFGCall.resume_arguments cont output
  have nm : next.store = output.store := rfl
  have nl : next.label = (if use256 then .l1027bc else .l10235c) := hc
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt .l1027bc fr
        else LIR.Fn1022c0.frameAt .l10235c fr) := by
    rw [na, nm]
    cases use256 <;> exact ⟨o4', o22,
      o5.trans (congrArg (Value.mk 64) af5),
      o12.trans (congrArg (Value.mk 64) af12),
      o13.trans (congrArg (Value.mk 64) af13),
      o15.trans (congrArg (Value.mk 64) af15),
      o39.trans (congrArg (Value.mk 32) af39),
      o50.trans (congrArg (Value.mk 16) af50),
      o51.trans (congrArg (Value.mk 16) af51),
      aadOut, saved3, saved12, saved13, saved14, saved15, saved5,
      hretRead.of_frame hfWork, savedReturn, hretLow, hstack.of_frame hfWork, hroom, halign,
      hs0r.of_frame hfWork, (outSlot _ (by decide) (by decide)).trans hs0,
      hs1r.of_frame hfWork, (outSlot _ (by decide) (by decide)).trans hs1,
      hs2r.of_frame hfWork, (outSlot _ (by decide) (by decide)).trans hs2,
      hs3r.of_frame hfWork, (outSlot _ (by decide) (by decide)).trans hs3slot,
      hslotsSep, trivial⟩
  have ex : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hl]
    exact hexec
  have accepted : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hg, htag]
    cases use256 <;> rfl
  have step : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l102759 else .l1022f9), args, mem⟩, []⟩ =
      .next ⟨callee, [cont]⟩ := by rw [Program.step, hx]; rfl
  refine ⟨next, (Semantics.Reaches.single step).trans
    (CFGCall.exec_reaches_resume ex cont [] accepted), nl, working, ?_, hfFull,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [na] using ht
  · rw [na]; exact o3'
  · rw [na]; exact o14'
  · rw [nm, ← adst]; exact hp
  · change memLoad output.store (fr.rsp - 156) 32 = _
    rw [he] at l0
    exact (childLoad 156 32 (by decide) (by decide) (by decide)).trans l0
  · change memLoad output.store (fr.rsp - 160) 32 = _
    rw [he] at l1
    exact (childLoad 160 32 (by decide) (by decide) (by decide)).trans l1
  · change memLoad output.store (fr.rsp - 164) 32 = _
    rw [he] at l2
    exact (childLoad 164 32 (by decide) (by decide) (by decide)).trans l2
  · change memLoad output.store (fr.rsp - 144) 64 = _
    rw [he] at lkey
    exact (childLoad 144 64 (by decide) (by decide) (by decide)).trans lkey

end AesGcm.Proofs.Machine.Core.Decrypt
