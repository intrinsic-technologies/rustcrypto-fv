import AesGcm.Proofs.Machine.Core.Decrypt.TagMemory
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.Machine.Tag.Main
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem tag_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (h mask : Vector UInt8 16) (aad ciphertext : ByteArray)
    (source destination : BitVec 64) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l1027bc fr
        else LIR.Fn1022c0.frameAt .l10235c fr))
    (hTypes : GPRsTyped args)
    (hctx : Readable mem fr.rdi 32)
    (hk0 : memLoad mem fr.rdi 64 = (GHASH.polyvalKeyWords
      (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1)
    (hk1 : memLoad mem (fr.rdi + 8) 64 = (GHASH.polyvalKeyWords
      (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2)
    (hz0 : memLoad mem (fr.rdi + 16) 64 = 0)
    (hz1 : memLoad mem (fr.rdi + 24) 64 = 0)
    (hmask : (span (fr.rsp - 96) 16).HasBytes mem ⟨mask.toArray⟩)
    (haad : Readable mem fr.rdx aad.size)
    (haadBytes : (span fr.rdx aad.size).HasBytes mem aad)
    (haadLen : fr.rcx.toNat = aad.size)
    (hbuffer : BufferIn mem fr.r8 source destination ciphertext)
    (hlen : (args[14].get 64).toNat = ciphertext.size)
    (hctxSep : (callStack fr).Disjoint (span fr.rdi 32))
    (haadSep : (callStack fr).Disjoint (span fr.rdx aad.size))
    (hbufferSep : (callStack fr).Disjoint (span fr.r8 24))
    (hsourceSep : (callStack fr).Disjoint (span source ciphertext.size)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l1027bc else .l10235c), args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l1027e8 else .l102388) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt .l1027e8 fr
          else LIR.Fn1022c0.frameAt .l102388 fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store
        [span (fr.rsp - BitVec.ofNat 64 (if use256 then 2912 else 2384))
          ((if use256 then 2912 else 2384) - 208),
         span (fr.rsp - 152) 8, span (fr.rsp - 80) 16] ∧
      next.arguments[3]'(by change 3 < 53; decide) = args[3] ∧
      next.arguments[14]'(by change 14 < 53; decide) = args[14] ∧
      next.arguments[12]'(by change 12 < 53; decide) = ⟨64, source⟩ ∧
      (span (fr.rsp - 80) 16).HasBytes next.store
        ⟨(Tag.authenticationTagFromMask h mask aad ciphertext).toArray⟩ := by
  let window : Nat := if use256 then 2912 else 2384
  have hwsize : 816 ≤ window := by cases use256 <;> decide
  have hworking' : args[4] = ⟨64, fr.rsp - 216⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[5] = ⟨64, fr.rcx⟩ ∧ args[12] = ⟨64, fr.rdi⟩ ∧
      args[13] = ⟨64, fr.r9⟩ ∧ args[15] = ⟨64, fr.r8⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 136) 64 = fr.rdx ∧
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
  obtain ⟨h4, h22, h5, h12, h13, h15, h39, h50, h51,
    haadLocal, hs3, hs12, hs13, hs14, hs15, hs5, hretRead, hret, hretLow, hstack, hroom, halign,
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
  have n152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by omega)
  have hsp : args[4].get 64 = fr.rsp - 216 := by rw [h4]; rfl
  have hcontext : args[12].get 64 = fr.rdi := by rw [h12]; rfl
  have hdescriptor : args[15].get 64 = fr.r8 := by rw [h15]; rfl
  have haadLength : args[5].get 64 = fr.rcx := by rw [h5]; rfl
  have he (off : BitVec 64) : args[4].get 64 + off = fr.rsp - (216 - off) := by
    rw [hsp]
    bv_omega
  have he224 : args[4].get 64 - 8 = fr.rsp - 224 := by rw [hsp]; bv_omega
  have hsetup : Writable code mem (args[4].get 64 - 8) 176 := by
    rw [he224]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨callee, cont, hx, hl, hc, hg, hm, c4, c7, c6, c2, c1, c8, c9, c12, keep, typed⟩ :=
    tag_runBlock use256 code hcode args mem hsetup
      (by rw [hsp]; apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _); cases use256 <;> decide +kernel)
      (by rw [hdescriptor]; exact hbuffer.1.of_offsets (addr_self _) (addr_self _) (by decide))
  let setupRegions := [span (fr.rsp - 224) 16, span (fr.rsp - 152) 8]
  have hfSetup : RamWriteFrame mem callee.store setupRegions := by
    rw [hm]
    have h64 : args[4].get 64 + 64 = fr.rsp - 152 := by rw [hsp]; bv_omega
    have hf := tagMemory_frame use256 args mem
      (by rw [hsp]; omega) (by rw [hsp]; have := hretRead.low; omega)
    rw [he224, h64] at hf
    exact hf
  have setupWithin : RegionsWithin setupRegions [fr.region] := by
    intro r hr
    simp only [setupRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, n224, n152] <;> omega
  have hfSetupFull : RamWriteFrame mem callee.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hfSetup setupWithin
  have descriptorOut := outside_activationRegion hbuffer.1 (by decide)
    (by omega) hbufferSep
  have buffer' := hbuffer.of_frame_disjoint hfSetupFull descriptorOut (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact span_disjoint_activationRegion hsourceSep)
  have ctxOut := outside_activationRegion hctx (by decide) (by omega) hctxSep
  have maskOut : Outside setupRegions (fr.rsp - 96) 16 := by
    refine ⟨by rw [n96]; have := hretRead.low; omega, ?_⟩
    intro r hr
    simp only [setupRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span, n224, n152, n96] <;> omega
  have mask' := hasBytes_of_frame hfSetup hmask maskOut.1 (outside_disjoint_span maskOut)
  have aad' := hasBytes_of_frame hfSetupFull haadBytes
    (Nat.le_trans haad.low (by decide)) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact span_disjoint_activationRegion haadSep)
  have descriptorApart : RangeApart (args[4].get 64 + 64) 8 fr.r8 8 := by
    rw [he]
    change RangeApart (fr.rsp - 152) 8 fr.r8 8
    have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      fr.r8.toNat 24 (by omega) (by decide) hbufferSep
    apply RangeApart.of_toNat
    · rw [n152]; have := hretRead.low; omega
    · have := hbuffer.1.low; omega
    · rw [n152]; omega
  have sourceLoad : memLoad (memStore mem (args[4].get 64 + 64) (args[15].get 64))
      (args[15].get 64) 64 = source := by
    rw [hdescriptor, memLoad_memStore_of_rangeApart _ _ _ _ _ descriptorApart]
    exact hbuffer.2.1
  have loads := tagMemory_loads use256 args mem
  rw [← hm, he, hdescriptor, he224] at loads
  obtain ⟨descriptorLocal, lengthLocal, returnLocal⟩ := loads
  change memLoad callee.store (fr.rsp - 152) 64 = fr.r8 at descriptorLocal
  let lower := fr.rsp - BitVec.ofNat 64 window
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x1027e8 else 0x102388) lower
  have asp : af.rsp = fr.rsp - 224 := by change (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = _; rw [c4]; exact he224
  have alow : af.low = lower := rfl
  have adst : af.rdi = fr.rsp - 80 := by change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _; rw [c7]; exact he 136
  have actx : af.rsi = fr.rdi := by change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _; rw [c6, hcontext]; rfl
  have amask : af.rdx = fr.rsp - 96 := by change (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = _; rw [c2]; exact he 120
  have aaad : af.rcx = fr.rdx := by change (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = _; rw [c1]; change memLoad mem (args[4].get 64 + 80) 64 = _; rw [he]; exact haadLocal
  have alen : af.r8 = fr.rcx := by change (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = _; rw [c8]; exact haadLength
  have asource : af.r9 = source := by change (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = _; rw [c9]; exact sourceLoad
  have ahigh : lower.toNat = fr.rsp.toNat - window := hsub _ (by omega)
  have childSep (ptr : BitVec 64) (n : Nat)
      (hd : (callStack fr).Disjoint (span ptr n)) :
      (callStack af).Disjoint (span ptr n) := by
    intro x hx hy
    apply hd x ?_ hy
    change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
    simp only [MemoryRegion.Contains, callStack, asp, alow, ahigh, n224] at hx
    omega
  have slotOut (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238) : Outside setupRegions ptr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [setupRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span, n224, n152] <;> omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).callSlots af) := by
    have s0 := (hfSetup.memLoad_eq (slotOut _ (by decide) (by decide))).trans hs0
    have s2 := (hfSetup.memLoad_eq (slotOut _ (by decide) (by decide))).trans hs2
    have apart : 0x201230 + 592 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208 := by
      rw [asp, n224]
      omega
    cases use256 <;> exact ⟨hs0r.of_frame hfSetup, s0, hs2r.of_frame hfSetup, s2, apart, trivial⟩
  have c39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ :=
    (keep 39 (by decide)).trans h39
  have c50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ :=
    (keep 50 (by decide)).trans h50
  have c51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ :=
    (keep 51 (by decide)).trans h51
  have childWritable : Writable code callee.store (af.rsp - 592) 592 := by
    rw [asp]
    have addr : fr.rsp - 224 - 592 = fr.rsp - 816 := by bv_omega
    rw [addr]
    apply (hstack.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have cw : (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).window = 592 := by
    cases use256 <;> rfl
  obtain ⟨output, hexec, htag, hdone, ht, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l101c20 else .l101800)
      (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo)
      (fun fr ↦ [span fr.rdi 16]) _ _ (Tag.tag_call use256 code hcode h mask aad ciphertext)
      callee.store callee.arguments (if use256 then 0x1027e8 else 0x102388) lower
      (typed hTypes) (by rw [c39]; rfl) (by rw [c50]; rfl) (by rw [c51]; rfl)
      ((keep 22 (by decide)).trans h22)
      (by change Readable callee.store af.rsp 8; rw [asp, ← he224]; exact (hsetup.readable.of_frame hfSetup).of_offsets (addr_self _) (addr_self _) (by decide))
      (by change memLoad callee.store af.rsp 64 = _; rw [asp]; exact returnLocal)
      (by cases use256 <;> decide)
      (by intro _; cases use256 <;> exact childWritable)
      (by rw [cw]; change lower.toNat + 592 ≤ af.rsp.toNat; rw [asp, ahigh, n224]; omega)
      (by change af.rsp.toNat % 16 = 8; rw [asp, n224]; omega)
      hslots (by
        change Readable callee.store af.rsi 32 ∧
          memLoad callee.store af.rsi 64 = _ ∧ memLoad callee.store (af.rsi + 8) 64 = _ ∧
          memLoad callee.store (af.rsi + 16) 64 = 0 ∧ memLoad callee.store (af.rsi + 24) 64 = 0 ∧
          Readable callee.store af.rdx 16 ∧ (span af.rdx 16).HasBytes callee.store ⟨mask.toArray⟩ ∧
          Readable callee.store af.rcx aad.size ∧ (span af.rcx aad.size).HasBytes callee.store aad ∧
          af.r8.toNat = aad.size ∧ (0 < ciphertext.size → Readable callee.store af.r9 ciphertext.size) ∧
          (span af.r9 ciphertext.size).HasBytes callee.store ciphertext ∧
          Readable callee.store (af.rsp + 8) 8 ∧
          (memLoad callee.store (af.rsp + 8) 64).toNat = ciphertext.size ∧
          aad.size ≤ AesGcm.Spec.GCM.maxAssociatedDataBytes ∧
          ciphertext.size ≤ AesGcm.Spec.GCM.maxMessageBytes ∧
          Writable code callee.store af.rdi 16 ∧
          (callStack af).Disjoint (span af.rdi 16) ∧
          (callStack af).Disjoint (span af.rsi 32) ∧
          (callStack af).Disjoint (span af.rdx 16) ∧
          (callStack af).Disjoint (span af.rcx aad.size) ∧
          (callStack af).Disjoint (span af.r9 ciphertext.size)
        rw [actx, amask, aaad, alen, asource, asp, adst]
        refine ⟨hctx.of_frame hfSetup, (hfSetupFull.memLoad_eq ?_).trans hk0,
          (hfSetupFull.memLoad_eq ?_).trans hk1, (hfSetupFull.memLoad_eq ?_).trans hz0,
          (hfSetupFull.memLoad_eq ?_).trans hz1, ?_, mask', haad.of_frame hfSetup,
          aad', haadLen, (fun _ ↦ buffer'.2.2.2.2.1), buffer'.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [BitVec.add_zero] using outside_subregion (offset := 0) (count := 8) ctxOut (by decide) (by decide)
        · exact outside_subregion (offset := 8) (count := 8) ctxOut (by decide) (by decide)
        · exact outside_subregion (offset := 16) (count := 8) ctxOut (by decide) (by decide)
        · exact outside_subregion (offset := 24) (count := 8) ctxOut (by decide) (by decide)
        · apply (hstack.readable.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel
        · have addr : fr.rsp - 224 + 8 = fr.rsp - 216 := by bv_omega
          rw [addr]
          apply (hstack.readable.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel
        · have addr : fr.rsp - 224 + 8 = fr.rsp - 216 := by bv_omega
          rw [addr, ← hsp, lengthLocal]
          exact hlen
        · have := haad.low
          change aad.size ≤ 2^61 - 1
          omega
        · have := hbuffer.2.2.2.2.1.low
          change ciphertext.size ≤ 2^36 - 32
          omega
        · apply (hstack.of_frame hfSetup).of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel
        · intro x hx hy
          simp only [MemoryRegion.Contains, callStack, asp, alow, ahigh, span, n224, n80] at hx hy
          omega
        · exact childSep _ _ hctxSep
        · intro x hx hy
          simp only [MemoryRegion.Contains, callStack, asp, alow, ahigh, span, n224, n96] at hx hy
          omega
        · exact childSep _ _ haadSep
        · exact childSep _ _ hsourceSep)
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi 16] at hf
  change (span af.rdi 16).HasBytes output.store _ at hp
  let writes := [span lower (window - 208), span (fr.rsp - 152) 8, span (fr.rsp - 80) 16]
  have setupWithinWrites : RegionsWithin setupRegions writes := by
    intro r hr
    simp only [setupRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨span lower (window - 208), by simp [writes], ?_, ?_⟩ <;>
        simp only [span, ahigh, n224] <;> omega
    · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  have childWithinWrites : RegionsWithin [af.region, span af.rdi 16] writes := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨span lower (window - 208), by simp [writes], ?_, ?_⟩ <;>
        simp only [span, Activation.region, alow, asp, ahigh, n224] <;> omega
    · rw [adst]
      exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  have hfWork : RamWriteFrame mem output.store writes :=
    ((RamWriteFrame.refl _ _).trans hfSetup setupWithinWrites).trans hf childWithinWrites
  have savedLoad (off : Nat) (ho : off ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
    apply hfWork.memLoad_eq
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [span, ahigh, n152, n80, hsub off (by omega)] <;> omega
  have childLoad (off : Nat) (hoff : 88 ≤ off) (ho : off ≤ 216) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad callee.store (fr.rsp - BitVec.ofNat 64 off) 64 := by
    apply hf.memLoad_eq
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Activation.region, alow, asp, ahigh, n224, hsub off (by omega)]
      omega
    · simp only [span, adst, n80, hsub off (by omega)]
      omega
  have savedReturn : memLoad output.store fr.rsp 64 = fr.ret := by
    have h := savedLoad 0 (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans hret
  have aadSetup : memLoad callee.store (fr.rsp - 136) 64 = fr.rdx := by
    apply Eq.trans (hfSetup.memLoad_eq _) haadLocal
    refine ⟨by rw [n136]; have := hretRead.low; omega, ?_⟩
    intro r hr
    simp only [setupRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span, n224, n152, n136] <;> omega
  have aadOut := (childLoad 136 (by decide) (by decide)).trans aadSetup
  have descriptorOut := (childLoad 152 (by decide) (by decide)).trans descriptorLocal
  have outSlot (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238) : memLoad output.store ptr 64 = memLoad mem ptr 64 := by
    apply hfWork.memLoad_eq
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [span, ahigh, n152, n80] <;> omega
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
  have af12 : af.r12 = source := by
    change (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = _
    rw [c12]
    exact asource
  have af13 : af.r13 = fr.r9 := by
    change (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = _
    exact congrArg (Value.get 64) ((keep 13 (by decide)).trans h13)
  have af14 : af.r14 = args[14].get 64 := congrArg (Value.get 64) (keep 14 (by decide))
  have af15 : af.r15 = fr.r8 := by
    change (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = _
    exact congrArg (Value.get 64) ((keep 15 (by decide)).trans h15)
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
  have nl : next.label = (if use256 then .l1027e8 else .l102388) := hc
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt .l1027e8 fr
        else LIR.Fn1022c0.frameAt .l102388 fr) := by
    rw [na, nm]
    cases use256 <;> exact ⟨o4', o22,
      o5.trans (congrArg (Value.mk 64) af5),
      o13.trans (congrArg (Value.mk 64) af13),
      o15.trans (congrArg (Value.mk 64) af15),
      o39.trans (congrArg (Value.mk 32) af39),
      o50.trans (congrArg (Value.mk 16) af50),
      o51.trans (congrArg (Value.mk 16) af51),
      descriptorOut, aadOut,
      (savedLoad 48 (by decide)).trans hs3,
      (savedLoad 40 (by decide)).trans hs12,
      (savedLoad 32 (by decide)).trans hs13,
      (savedLoad 24 (by decide)).trans hs14,
      (savedLoad 16 (by decide)).trans hs15,
      (savedLoad 8 (by decide)).trans hs5,
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
      ⟨⟨(if use256 then .l1027bc else .l10235c), args, mem⟩, []⟩ =
      .next ⟨callee, [cont]⟩ := by rw [Program.step, hx]; rfl
  refine ⟨next, (Semantics.Reaches.single step).trans
    (CFGCall.exec_reaches_resume ex cont [] accepted), nl, working, ?_, hfWork,
    ?_, ?_, ?_, ?_⟩
  · simpa only [na] using ht
  · rw [na]; exact o3'
  · rw [na]; exact o14'
  · rw [na, o12, af12]
  · rw [nm, ← adst]; exact hp

end AesGcm.Proofs.Machine.Core.Decrypt
