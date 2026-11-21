import AesGcm.Proofs.Machine.Core.Encrypt.Calls
import AesGcm.Proofs.Machine.Core.Encrypt.Finish
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.Machine.Tag.Main
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem authenticate (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (mask : Vector UInt8 16)
    (destination : BitVec 64) (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l102b3e else .l1026de))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr))
    (hTypes : GPRsTyped loc.arguments)
    (hinputs : InputsIn use256 key nonce associatedData loc.store fr.rsi fr.rdx fr.rcx fr.r8)
    (hcipherRead : 0 < ciphertext.size → Readable loc.store destination ciphertext.size)
    (hcipher : (span destination ciphertext.size).HasBytes loc.store ciphertext)
    (hmask : (span (fr.rsp - 80) 16).HasBytes loc.store ⟨mask.toArray⟩)
    (hlength : ((loc.arguments[5]'(by change 5 < 53; decide)).get 64).toNat = ciphertext.size)
    (hdest : (loc.arguments[13]'(by change 13 < 53; decide)).get 64 = destination)
    (haadBound : associatedData.size ≤ AesGcm.Spec.GCM.maxAssociatedDataBytes)
    (hcipherBound : ciphertext.size ≤ AesGcm.Spec.GCM.maxMessageBytes)
    (hw : Writable code loc.store fr.rdi 17)
    (hstackSep : ∀ region ∈ [span fr.rsi (GcmContext.size (AES16.variant use256)),
      span fr.rdx 12, span fr.rcx associatedData.size, span destination ciphertext.size, span fr.rdi 17],
      (callStack fr).Disjoint region)
    (hresultSep : (span fr.rdi 17).Disjoint (span destination ciphertext.size)) :
    ∃ output,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102980.frameInfo else LIR.Fn102520.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame loc.store output.store [fr.region, span fr.rdi 17] ∧
      output.store[fr.rdi]? = some 0 ∧
      (span destination ciphertext.size).HasBytes output.store ciphertext ∧
      (span (fr.rdi + 1) 16).HasBytes output.store
        ⟨(Tag.authenticationTagFromMask
          (Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0))
          mask associatedData ciphertext).toArray⟩ := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hworking hTypes hinputs hcipherRead hcipher hmask hlength hdest hw ⊢
  subst label
  let window : Nat := if use256 then 0xb50 else 0x940
  let slotHigh : Nat := if use256 then 0x201d80 else 0x201b70
  have facts :
      args[4] = ⟨64, fr.rsp - 200⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 112) 64 = fr.rdi ∧ memLoad mem (fr.rsp - 104) 64 = fr.rsi ∧
      memLoad mem (fr.rsp - 96) 64 = fr.rcx ∧ memLoad mem (fr.rsp - 88) 64 = fr.r8 ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  rcases facts with ⟨h4, h22, h39, h50, h51, srdi, srsi, srcx, sr8,
    s3, s12, s13, s14, s15, s5, hretRead, hret, hretLow, hstack, hroom, halign,
    hslot0Read, hslot0, hslot2Read, hslot2, hslotSep, -⟩
  have h4get : args[4].get 64 = fr.rsp - 200 := by rw [h4]; rfl
  have hwindow : 208 + 592 ≤ window := by cases use256 <;> decide
  have hretBound := hretRead.low
  have hresultBound := hw.readable.low
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by change n % 2^64 ≤ fr.rsp.toNat; omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := fr.rsp.isLt
      omega)]
  let lower := fr.rsp - BitVec.ofNat 64 window
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hs208 : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := hsub 208 (by omega)
  have hs200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
  have hs80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := hsub 80 (by omega)
  have hs48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := hsub 48 (by omega)
  have hrdi1 : (fr.rdi + 1).toNat = fr.rdi.toNat + 1 := by bv_omega
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ :=
    tag_runBlock use256 code hcode args mem
      (by
        rw [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega]
        apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
        cases use256 <;> decide +kernel)
      (by
        rw [h4get, show fr.rsp - 200 + 88 = fr.rsp - 112 by bv_omega]
        apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
        cases use256 <;> decide +kernel)
  have hmem : RamWriteFrame mem callee.store [span (fr.rsp - 208) 16] := by
    rw [hcalleeMem]
    have hf := tagMemory_frame use256 args mem
      (by rw [h4get, hs200]; omega) (by rw [h4get, hs200]; omega)
    simpa only [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega] using hf
  have spanWithin : RegionsWithin [span (fr.rsp - 208) 16] [fr.region] := by
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    exact ⟨fr.region, by simp only [List.mem_singleton], by simp only [span, Activation.region, hs208]; omega,
      by simp only [span, Activation.region, hs208]; omega⟩
  have stackOutside {base : BitVec 64} {count : Nat} (hp : 0 < count)
      (hr : Readable mem base count) (hsep : (callStack fr).Disjoint (span base count)) :
      Outside [span (fr.rsp - 208) 16] base count := by
    have hb := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      base.toNat count (by omega) hp hsep
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs208]
    omega
  have stackDisjoint {base : BitVec 64} {count : Nat}
      (hsep : (callStack fr).Disjoint (span base count)) :
      ∀ r ∈ [span (fr.rsp - 208) 16], (span base count).Disjoint r := by
    intro r hin x hx hy
    obtain rfl := List.mem_singleton.mp hin
    apply hsep x ?_ hx
    simp only [MemoryRegion.Contains, callStack, span, hs208] at hy ⊢
    omega
  have hi := hinputs.of_frame_disjoint hmem
    (stackOutside (by cases use256 <;> decide) hinputs.2.1 (hstackSep _ (by simp)))
    (stackOutside (by decide) hinputs.2.2.1 (hstackSep _ (by simp)))
    (stackDisjoint (hstackSep _ (by simp)))
  have hcipherBound64 : destination.toNat + ciphertext.size ≤ 2^64 := by
    by_cases hp : 0 < ciphertext.size
    · have := (hcipherRead hp).low
      omega
    · have := destination.isLt
      omega
  have hcbytes := hasBytes_of_frame hmem hcipher hcipherBound64
    (stackDisjoint (hstackSep _ (by simp)))
  have hmbytes := hasBytes_of_frame hmem hmask (by simp only [span, hs80]; omega) (by
    intro r hin x hx hy
    obtain rfl := List.mem_singleton.mp hin
    simp only [MemoryRegion.Contains, span, hs80, hs208] at hx hy
    omega)
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 208 := by
    rw [hc4, h4get]; bv_omega
  have hcallee2 : (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = fr.rsp - 80 := by
    rw [hc2, h4get]; bv_omega
  have hcallee3 : (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.rdi := by
    rw [hc3, h4get, show fr.rsp - 200 + 88 = fr.rsp - 112 by bv_omega, srdi]
  have hcallee1 : (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = fr.rcx := by
    rw [hc1, h4get, show fr.rsp - 200 + 104 = fr.rsp - 96 by bv_omega, srcx]
  have hcallee6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = fr.rsi := by
    rw [hc6, h4get, show fr.rsp - 200 + 96 = fr.rsp - 104 by bv_omega, srsi]
  have hcallee7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = fr.rdi + 1 := by
    rw [hc7, h4get, show fr.rsp - 200 + 88 = fr.rsp - 112 by bv_omega, srdi]
  have hcallee8 : (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = fr.r8 := by
    rw [hc8, h4get, show fr.rsp - 200 + 112 = fr.rsp - 88 by bv_omega, sr8]
  have hcallee9 : (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = destination := hc9.trans hdest
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x102b67 else 0x102707) lower
  have hafsp : af.rsp = fr.rsp - 208 := hcallee4
  have hafsrc : af.rsi = fr.rsi := hcallee6
  have hafmask : af.rdx = fr.rsp - 80 := hcallee2
  have hafdst : af.rdi = fr.rdi + 1 := hcallee7
  have hafaad : af.rcx = fr.rcx := hcallee1
  have haflen : af.r8 = fr.r8 := hcallee8
  have hafcipher : af.r9 = destination := hcallee9
  have haflow : af.low = lower := rfl
  have htagWindow : (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).window = 592 := by
    cases use256 <;> rfl
  have hresultStack := hstackSep (span fr.rdi 17) (by simp)
  have hcontextStack := hstackSep (span fr.rsi (GcmContext.size (AES16.variant use256))) (by simp)
  have resultBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 17 (by omega) (by decide) hresultStack
  have inputApart (base : BitVec 64) (count : Nat)
      (hsep : (callStack fr).Disjoint (span base count)) :
      (callStack af).Disjoint (span base count) := by
    intro x hx hy
    apply hsep x ?_ hy
    simp only [MemoryRegion.Contains, callStack, hafsp, haflow, hlower, hs208] at hx ⊢
    omega
  have hpre :
      let k := GHASH.polyvalKeyWords
        (GcmContext.blockWord (Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0)) 1)
        (GcmContext.blockWord (Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0)) 0)
      Readable callee.store af.rsi 32 ∧ memLoad callee.store af.rsi 64 = k.1 ∧
      memLoad callee.store (af.rsi + 8) 64 = k.2 ∧ memLoad callee.store (af.rsi + 16) 64 = 0 ∧
      memLoad callee.store (af.rsi + 24) 64 = 0 ∧
      Readable callee.store af.rdx 16 ∧ (span af.rdx 16).HasBytes callee.store ⟨mask.toArray⟩ ∧
      Readable callee.store af.rcx associatedData.size ∧
      (span af.rcx associatedData.size).HasBytes callee.store associatedData ∧
      af.r8.toNat = associatedData.size ∧ (0 < ciphertext.size → Readable callee.store af.r9 ciphertext.size) ∧
      (span af.r9 ciphertext.size).HasBytes callee.store ciphertext ∧
      Readable callee.store (af.rsp + 8) 8 ∧
      (memLoad callee.store (af.rsp + 8) 64).toNat = ciphertext.size ∧
      associatedData.size ≤ AesGcm.Spec.GCM.maxAssociatedDataBytes ∧
      ciphertext.size ≤ AesGcm.Spec.GCM.maxMessageBytes ∧ Writable code callee.store af.rdi 16 ∧
      (callStack af).Disjoint (span af.rdi 16) ∧ (callStack af).Disjoint (span af.rsi 32) ∧
      (callStack af).Disjoint (span af.rdx 16) ∧
      (callStack af).Disjoint (span af.rcx associatedData.size) ∧
      (callStack af).Disjoint (span af.r9 ciphertext.size) := by
    dsimp only
    rw [hafsrc, hafmask, hafaad, haflen, hafcipher, hafsp, hafdst]
    rcases hi with ⟨hctx, hctxRead, _, _, haRead, haBytes, haLen⟩
    refine ⟨?_, hctx.2.1, hctx.2.2.1, hctx.2.2.2.1, hctx.2.2.2.2,
      ?_, hmbytes, haRead, haBytes, haLen, (fun hp ↦ (hcipherRead hp).of_frame hmem), hcbytes,
      ?_, ?_, haadBound, hcipherBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hctxRead.of_offsets (addr_self _) (addr_self _) (by cases use256 <;> decide)
    · apply (hstack.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    · rw [show fr.rsp - 208 + 8 = fr.rsp - 200 by bv_omega]
      apply (hstack.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    · rw [show fr.rsp - 208 + 8 = fr.rsp - 200 by bv_omega, hcalleeMem]
      have hh : memLoad (tagMemory use256 args mem) (args[4].get 64) 64 = args[5].get 64 := by
        simp only [tagMemory]
        rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_diff; bv_omega),
          memLoad_memStore_same _ _ _ (by decide) (by decide)]
      rw [h4get] at hh
      rw [hh]
      exact hlength
    · exact (hw.of_frame hmem).of_offsets rfl (addr_self _) (by decide)
    · intro x hx hy
      apply hresultStack x ?_ ?_
      · simp only [MemoryRegion.Contains, callStack, hafsp, haflow, hlower, hs208] at hx ⊢; omega
      · simp only [MemoryRegion.Contains, span, hrdi1] at hy ⊢; omega
    · intro x hx hy
      apply inputApart fr.rsi (GcmContext.size (AES16.variant use256)) hcontextStack x hx
      simp only [MemoryRegion.Contains, span, GcmContext.size] at hy ⊢
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, hafsp, haflow, hlower, hs208, hs80] at hx hy
      omega
    · exact inputApart _ _ (hstackSep _ (by simp))
    · exact inputApart _ _ (hstackSep _ (by simp))
  have slotOutside (address : BitVec 64) (hlo : 0x201208 ≤ address.toNat)
      (hhi : address.toNat + 8 ≤ 0x201230) : Outside [span (fr.rsp - 208) 16] address 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    have hhigh : 0x201230 + 208 ≤ slotHigh := by cases use256 <;> decide
    simp only [span, hs208]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).callSlots af) := by
    have s0 := (hmem.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hslot0
    have s2 := (hmem.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans hslot2
    have hhigh : 0x201230 + 592 + 208 ≤ slotHigh := by cases use256 <;> decide
    have sep : 0x201230 + 592 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208 := by
      rw [hafsp, hs208]
      omega
    cases use256 <;> exact ⟨hslot0Read.of_frame hmem, s0, hslot2Read.of_frame hmem, s2, sep, trivial⟩
  have hc39' := hc39.trans h39
  have hc50' := hc50.trans h50
  have hc51' := hc51.trans h51
  obtain ⟨tagged, htagExec, htagReturn, htagDone, htagTypes, htagFrame, htagPost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l101c20 else .l101800)
      (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo)
      (fun fr ↦ [span fr.rdi 16]) _ _
      (Tag.tag_call use256 code hcode
        (Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0))
        mask associatedData ciphertext)
      callee.store callee.arguments (if use256 then 0x102b67 else 0x102707) lower
      (hcalleeTypes hTypes) (by rw [hc39']; rfl) (by rw [hc50']; rfl) (by rw [hc51']; rfl)
      (hc22.trans h22)
      (by rw [hcallee4]; apply (hstack.readable.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel)
      (by rw [hcalleeMem, hc4]; simp only [tagMemory]
          exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro _; rw [htagWindow, hcallee4, BitVec.sub_sub]
          apply (hstack.of_frame hmem).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel)
      (by rw [htagWindow, hcallee4, hlower, hs208]; omega)
      (by rw [hcallee4, hs208]; omega) hslots hpre
  change Atom.All code tagged.values tagged.store
    ((if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).doneAtoms af) at htagDone
  change RamWriteFrame callee.store tagged.store [af.region, span af.rdi 16] at htagFrame
  change (span af.rdi 16).HasBytes tagged.store _ at htagPost
  rw [hafdst] at htagPost
  have hdone' : tagged.values[4] = ⟨64, af.rsp + 8⟩ ∧ tagged.values[22] = ⟨1, 0⟩ ∧
      tagged.values[3] = ⟨64, af.rbx⟩ ∧ tagged.values[5] = ⟨64, af.rbp⟩ ∧
      tagged.values[12] = ⟨64, af.r12⟩ ∧ tagged.values[13] = ⟨64, af.r13⟩ ∧
      tagged.values[14] = ⟨64, af.r14⟩ ∧ tagged.values[15] = ⟨64, af.r15⟩ ∧
      tagged.values[39] = ⟨32, af.mxcsr⟩ ∧ tagged.values[50] = ⟨16, af.ftw⟩ ∧
      tagged.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact htagDone
  rcases hdone' with ⟨ho4, ho22, ho3, _, _, _, _, _, ho39, ho50, ho51, -⟩
  have hfTight : RamWriteFrame mem tagged.store
      [span lower (window - 192), span (fr.rdi + 1) 16] := by
    have hfirst : RamWriteFrame mem callee.store
        [span lower (window - 192), span (fr.rdi + 1) 16] := by
      apply (RamWriteFrame.refl _ _).trans hmem
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      exact ⟨span lower (window - 192), by simp, by simp only [span, hs208, hlower]; omega,
        by simp only [span, hs208, hlower]; omega⟩
    apply hfirst.trans htagFrame
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · exact ⟨span lower (window - 192), by simp,
        by simp only [span, Activation.region, haflow, hlower]; omega,
        by simp only [span, Activation.region, haflow, hafsp, hlower, hs208]; omega⟩
    · exact ⟨span (fr.rdi + 1) 16, by simp, by rw [hafdst]; exact Nat.le_refl _, by rw [hafdst]; exact Nat.le_refl _⟩
  have hf : RamWriteFrame mem tagged.store [fr.region, span fr.rdi 17] := by
    apply (RamWriteFrame.refl _ _).trans hfTight
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · exact ⟨fr.region, by simp, by simp only [span, Activation.region, hlower]; omega,
        by simp only [span, Activation.region, hlower]; omega⟩
    · exact ⟨span fr.rdi 17, by simp, by simp only [span, hrdi1]; omega,
        by simp only [span, hrdi1]; omega⟩
  have originalSaved (n : Nat) (hn : n ≤ 48) :
      memLoad tagged.store (fr.rsp - BitVec.ofNat 64 n) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 n) 64 := by
    apply hfTight.memLoad_eq
    refine ⟨by rw [hsub n (by omega)]; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [span, hlower, hsub n (by omega)]; omega
    · simp only [span, hrdi1, hsub n (by omega)]; omega
  have htsp : tagged.values[4].get 64 = fr.rsp - 200 := by
    rw [ho4]
    change af.rsp + 8 = _
    rw [hafsp]
    bv_omega
  have htresult : tagged.values[3].get 64 = fr.rdi := by rw [ho3]; exact hcallee3
  have hreadSaved : Readable tagged.store (fr.rsp - 48) 56 := by
    have pref : Readable mem (fr.rsp - 48) 48 :=
      hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by cases use256 <;> decide +kernel)
    have last : Readable mem (fr.rsp - 48 + BitVec.ofNat 64 48) 8 := by
      change Readable mem (fr.rsp - (48#64) + (48#64)) 8
      rw [BitVec.sub_add_cancel]
      exact hretRead
    exact (readable_append pref last).of_frame hf
  have af39 : af.mxcsr = fr.mxcsr := congrArg (fun v ↦ v.get 32) hc39'
  have af50 : af.ftw = fr.ftw := congrArg (fun v ↦ v.get 16) hc50'
  have af51 : af.fcw = fr.fcw := congrArg (fun v ↦ v.get 16) hc51'
  obtain ⟨output, hfinish, hstore, hreturn, hdone, _, houtputTypes, hstatusFrame, hstatus⟩ :=
    success_exec use256 code hcode fr tagged.values tagged.store htsp htresult
      ((hw.of_frame hf).of_offsets (addr_self _) (addr_self _) (by decide)) hreadSaved
      (by rw [hs48]; omega)
      ((show memLoad tagged.store fr.rsp 64 = memLoad mem fr.rsp 64 from by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using originalSaved 0 (by decide)).trans hret)
      hretLow
      ⟨(originalSaved 48 (by decide)).trans s3, (originalSaved 40 (by decide)).trans s12,
        (originalSaved 32 (by decide)).trans s13, (originalSaved 24 (by decide)).trans s14,
        (originalSaved 16 (by decide)).trans s15, (originalSaved 8 (by decide)).trans s5⟩
      ho22 (ho39.trans (congrArg (Value.mk 32) af39))
      (ho50.trans (congrArg (Value.mk 16) af50)) (ho51.trans (congrArg (Value.mk 16) af51)) htagTypes
  have hfull : RamWriteFrame mem output.store [fr.region, span fr.rdi 17] := by
    apply hf.trans hstatusFrame
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    exact ⟨span fr.rdi 17, by simp, Nat.le_refl _, by simp only [span]; omega⟩
  refine ⟨output, ?_, hreturn, hdone, houtputTypes, hfull, hstatus, ?_, ?_⟩
  · apply CFGCall.exec_call hcall
    · change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ tagged
      rw [hcalleeLabel]
      exact htagExec
    · simp only [StackFrame.Accepts, hguard, htagReturn]
      cases use256 <;> rfl
    · have ha := CFGCall.resume_arguments continuation tagged
      have hl : (continuation.resume tagged).label = (if use256 then .l102b67 else .l102707) := htarget
      have hs : (continuation.resume tagged).store = tagged.store := rfl
      have he : continuation.resume tagged =
          ⟨(if use256 then .l102b67 else .l102707), tagged.values, tagged.store⟩ := by
        cases hloc : continuation.resume tagged with
        | mk label arguments store =>
          rw [hloc] at ha hl hs
          dsimp only at ha hl hs
          subst label arguments store
          rfl
      rw [he]
      exact hfinish
  · apply hasBytes_of_frame hfull hcipher hcipherBound64
    intro r hin x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · apply hstackSep _ (by simp) x ?_ hx
      simp only [MemoryRegion.Contains, callStack, Activation.region] at hy ⊢
      omega
    · exact hresultSep x hy hx
  · apply hasBytes_of_frame hstatusFrame
      htagPost
      (by simp only [span, hrdi1]; omega)
    intro r hin x hx hy
    obtain rfl := List.mem_singleton.mp hin
    simp only [MemoryRegion.Contains, span, hrdi1] at hx hy
    omega

end AesGcm.Proofs.Machine.Core.Encrypt
