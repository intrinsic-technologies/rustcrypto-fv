import AesGcm.Proofs.Machine.Core.Decrypt.CTRContract
import AesGcm.Proofs.Machine.Core.Decrypt.FullBlocksMemory
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem fullBlocks_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (crypt : CTR.CryptCall use256 code key)
    (input : ByteArray)
    (length source destination : BitVec 64) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l102885 fr else LIR.Fn1022c0.frameAt .l102425 fr))
    (hTypes : GPRsTyped args)
    (hlen : args[14].get 64 = length) (hsource : args[12].get 64 = source)
    (hcounter : args[15].get 64 = fr.rsp - 120)
    (hmask : args[3].get 64 = 0xfffffffe0)
    (hbound : length.toNat ≤ 2^32) (hpos : 16 < length.toNat)
    (hsize : input.size = 16 * (length.toNat / 16))
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rdi + 32) mem)
    (hrSchedule : Readable mem (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)))
    (hkeyPtr : memLoad mem (fr.rsp - 128) 64 = fr.rdi + 32)
    (hdescWrite : Writable code mem (fr.r8 + 8) 8)
    (hdescDestination : memLoad mem (fr.r8 + 8) 64 = destination)
    (hread : Readable mem source input.size)
    (hbytes : (span source input.size).HasBytes mem input)
    (hwrite : Writable code mem destination input.size)
    (halias : source = destination ∨ (span source input.size).Disjoint (span destination input.size))
    (hstackSep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size, span (fr.r8 + 8) 8],
      (callStack fr).Disjoint r)
    (hdescSep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size], (span (fr.r8 + 8) 8).Disjoint r)
    (hdataSep : (span destination input.size).Disjoint
      (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))))
    (hslotSep : ∀ slot ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64)),
      (span destination input.size).Disjoint (span slot 8) ∧
      (span (fr.r8 + 8) 8).Disjoint (span slot 8)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l102885 else .l102425),args,mem⟩,[]⟩ ⟨next,[]⟩ ∧
      next.label = (if use256 then .l1028d0 else .l102470) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt .l1028d0 fr else LIR.Fn1022c0.frameAt .l102470 fr) ∧
      GPRsTyped next.arguments ∧ RamWriteFrame mem next.store
        [span (fr.rsp - BitVec.ofNat 64 (if use256 then 2912 else 2384))
          ((if use256 then 2912 else 2384) - 100), span (fr.r8 + 8) 8, span destination input.size] ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 8 = args[0].get 8 ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = source + BitVec.ofNat 64 input.size ∧
      (next.arguments[14]'(by change 14 < 53; decide)).get 64 = BitVec.ofNat 64 (length.toNat % 16) ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 = fr.rsp - 120 ∧
      memLoad next.store (fr.r8 + 8) 64 = destination + BitVec.ofNat 64 input.size ∧
      memLoad next.store (fr.rsp - 104) 32 = memLoad mem (fr.rsp - 104) 32 + BitVec.ofNat 32 (length.toNat / 16) ∧
      Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock next.store (fr.rsp - 120)) =
        Nat.repeat (Standards.NIST.GCM.inc 32) (length.toNat / 16)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (fr.rsp - 120))) ∧
      (span destination input.size).HasBytes next.store (AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (fr.rsp - 120)))
          (AesGcm.Spec.GCM.bitsOfByteArray input))) ∧
      memLoad next.store (fr.rsp - 128) 64 = fr.rdi + 32 := by
  let window : Nat := if use256 then 2912 else 2384
  let ctrWindow : Nat := if use256 then 2688 else 2160
  have hwsize : window = 224 + ctrWindow := by cases use256 <;> decide
  have hw224 : 224 ≤ window := by cases use256 <;> decide
  have hworking' : args[4] = ⟨64, fr.rsp - 216⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[5] = ⟨64, fr.rcx⟩ ∧
      args[13] = ⟨64, fr.r9⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 152) 64 = fr.r8 ∧
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
  obtain ⟨h4, h22, h5, h13, h39, h50, h51,
    descriptorLocal, haadLocal, hs3, hs12, hs13, hs14, hs15, hs5, hretRead, hret, hretLow, hstack, hroom, halign,
    hs0r, hs0, hs1r, hs1, hs2r, hs2, hs3r, hs3slot, hslotsSep, _⟩ := hworking'
  have hsub (off : Nat) (ho : off ≤ window) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off :=
    stack_sub_toNat fr hroom ho
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
  have n120 : (fr.rsp - 120).toNat = fr.rsp.toNat - 120 := hsub 120 (by omega)
  have n128 : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := hsub 128 (by omega)
  have n104 : (fr.rsp - 104).toNat = fr.rsp.toNat - 104 := hsub 104 (by omega)
  have n152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by omega)
  have hsp : args[4].get 64 = fr.rsp - 216 := by rw [h4]; rfl
  have offset (n : Nat) : args[4].get 64 + BitVec.ofNat 64 n =
      fr.rsp - 216 + BitVec.ofNat 64 n := by rw [hsp]
  have a224 : args[4].get 64 - 8 = fr.rsp - 224 := by rw [hsp]; bv_omega
  have a200 : args[4].get 64 + 16 = fr.rsp - 200 := by rw [hsp]; bv_omega
  have a192 : args[4].get 64 + 24 = fr.rsp - 192 := by rw [hsp]; bv_omega
  have a184 : args[4].get 64 + 32 = fr.rsp - 184 := by rw [hsp]; bv_omega
  have a176 : args[4].get 64 + 40 = fr.rsp - 176 := by rw [hsp]; bv_omega
  have a152 : args[4].get 64 + 64 = fr.rsp - 152 := by rw [hsp]; bv_omega
  have a128 : args[4].get 64 + 88 = fr.rsp - 128 := by rw [hsp]; bv_omega
  have hdescriptor : memLoad mem (args[4].get 64 + 64) 64 = fr.r8 := by
    rw [a152]; exact descriptorLocal
  have hsetup : Writable code mem (args[4].get 64 - 8) 56 := by
    rw [a224]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨callee,cont,hx,hl,hc,hg,hm,c4,c7,c6,c1,c2,c3,c13,c14,keep,typed⟩ :=
    full_ctr_runBlock use256 code hcode args mem hsetup
      (by rw [a152]; apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel)
      (by rw [hdescriptor]; exact hdescWrite)
  let setupRegions := [span (fr.rsp - 224) 56, span (fr.r8 + 8) 8]
  have hfSetup : RamWriteFrame mem callee.store setupRegions := by
    rw [hm]
    have hf := fullCtrMemory_frame use256 args mem
      (by rw [hsp]; omega) (by rw [hsp]; have := hretRead.low; omega)
      (by rw [hdescriptor]; have := hdescWrite.readable.low; omega)
    rw [a224,hdescriptor] at hf
    exact hf
  have localSep (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) :
      (span (fr.rsp - BitVec.ofNat 64 n) count).Disjoint (span (fr.r8 + 8) 8) :=
    local_span_disjoint_external hroom hn hc (hstackSep _ (by simp))
  have setupOutside (ptr : BitVec 64) (n : Nat)
      (hr : Readable mem ptr n) (hp : 0 < n)
      (hs : (callStack fr).Disjoint (span ptr n))
      (hd : (span (fr.r8 + 8) 8).Disjoint (span ptr n)) : Outside setupRegions ptr n := by
    refine ⟨Nat.le_trans hr.low (by decide), ?_⟩
    intro r hin
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · have sep := disjoint_bounds _ _ _ _ (by decide : 0 < 56) hp
        (local_span_disjoint_external hroom (by omega) (by decide) hs)
      exact sep.symm
    · have sep := disjoint_bounds _ _ _ _ (by decide : 0 < 8) hp hd
      exact sep.symm
  have hschedule' := AES16.scheduleIn_of_frame hschedule hfSetup
    (setupOutside _ _ hrSchedule (by cases use256 <;> decide)
      (hstackSep _ (by simp)) (hdescSep _ (by simp)))
  have hbytes' := hasBytes_of_frame hfSetup hbytes
    (Nat.le_trans hread.low (by decide)) (by
      intro r hin
      simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl
      · intro x hx hy
        exact local_span_disjoint_external hroom (by omega : 224 ≤ window) (by decide : 56 ≤ 224) (hstackSep (span source input.size) (by simp)) x hy hx
      · intro x hx hy
        exact hdescSep (span source input.size) (by simp) x hy hx)
  have setupLocal (n count : Nat) (hn : count ≤ n) (hp : 0 < count) (hlo : n ≤ 168) :
      Outside setupRegions (fr.rsp - BitVec.ofNat 64 n) count := by
    refine ⟨by rw [hsub n (by omega)]; have := hretRead.low; omega, ?_⟩
    intro r hin
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · simp only [span,n224,hsub n (by omega)]
      omega
    · have sep := disjoint_bounds _ _ _ _ hp (by decide : 0 < 8) (localSep n count (by omega) hn)
      exact sep
  have loads := fullCtrMemory_loads use256 args mem
  rw [← hm,a224,a200,a192,a184,a176,hcounter,hsource,hdescriptor,hdescDestination,hlen] at loads
  let lower := fr.rsp - BitVec.ofNat 64 window
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x1028d0 else 0x102470) lower
  have asp : af.rsp = fr.rsp - 224 := by
    change (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = _
    rw [c4]; exact a224
  have alow : af.low = lower := rfl
  have akey : af.rdi = fr.rsp - 128 := by
    change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _
    rw [c7]; exact a128
  have adesc : af.rsi = fr.rsp - 200 := by
    change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _
    rw [c6]; exact a200
  have ahigh : lower.toNat = fr.rsp.toNat - window := hsub _ (by omega)
  have localRead (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) :
      Readable callee.store (fr.rsp - BitVec.ofNat 64 n) count := by
    apply (hstack.readable.of_frame hfSetup).sub
    all_goals rw [hsub n hn,hsub window (Nat.le_refl _)]
    all_goals omega
  have localWrite (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) :
      Writable code callee.store (fr.rsp - BitVec.ofNat 64 n) count := by
    apply (hstack.of_frame hfSetup).sub
    all_goals rw [hsub n hn,hsub window (Nat.le_refl _)]
    all_goals omega
  have hkey : memLoad callee.store (fr.rsp - 128) 64 = fr.rdi + 32 :=
    (hfSetup.memLoad_eq (setupLocal 128 8 (by decide) (by decide) (by decide))).trans hkeyPtr
  have slotOutside (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238)
      (hd : (span (fr.r8 + 8) 8).Disjoint (span ptr 8)) : Outside setupRegions ptr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · simp only [span,n224]; omega
    · have sep := disjoint_bounds _ _ _ _ (by decide : 0 < 8) (by decide : 0 < 8) hd
      exact sep.symm
  have slotSaved (ptr : BitVec 64)
      (hin : ptr ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64))) :
      memLoad callee.store ptr 64 = memLoad mem ptr 64 := by
    apply hfSetup.memLoad_eq
    apply slotOutside ptr _ _ (hslotSep ptr hin).2
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    all_goals rcases hin with rfl | rfl | rfl | rfl <;> decide
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlots af) := by
    have s0 := (slotSaved _ (by simp)).trans hs0
    have s1 := (slotSaved _ (by simp)).trans hs1
    have s3 := (slotSaved _ (by simp)).trans hs3slot
    have sep : 0x201238 + ctrWindow ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208 := by
      rw [asp,n224]; omega
    cases use256 <;> exact ⟨hs0r.of_frame hfSetup,s0,hs1r.of_frame hfSetup,s1,
      hs3r.of_frame hfSetup,s3,sep,trivial⟩
  have counterSlot (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238) :
      (span (fr.rsp - 120) 20).Disjoint (span ptr 8) := by
    intro x hx hy
    simp only [MemoryRegion.Contains,span,n120] at hx hy
    omega
  have localApartExternal (n count : Nat) (hn : n ≤ window) (hc : count ≤ n)
      {base : BitVec 64} {size : Nat} (hs : (callStack fr).Disjoint (span base size)) :=
    local_span_disjoint_external hroom hn hc hs
  have localApart (n count m count' : Nat) (hn : n ≤ window) (hm : m ≤ window)
      (hc : count ≤ n) (hc' : count' ≤ m) (ha : m + count ≤ n ∨ n + count' ≤ m) :=
    stack_local_spans_disjoint hroom hn hm hc hc' ha
  have stackApartLocal (n count : Nat) (_hn : n ≤ window) (hc : count ≤ n) (htop : n ≤ 216) :=
    childStack_disjoint_local hroom (by omega : 224 ≤ window) alow asp
      (by omega : n + 8 ≤ 224) hc
  have stackApartExternal {base : BitVec 64} {size : Nat}
      (hs : (callStack fr).Disjoint (span base size)) :=
    childStack_disjoint_external hroom (by omega : 224 ≤ window) alow asp hs
  have hpre :
      Readable callee.store af.rdi 8 ∧ memLoad callee.store af.rdi 64 = fr.rdi + 32 ∧
      AES16.ScheduleIn (AES16.variant use256) key (fr.rdi + 32) callee.store ∧
      Readable callee.store (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rsi 32 ∧ memLoad callee.store af.rsi 64 = fr.rsp - 120 ∧
      memLoad callee.store (af.rsi + 8) 64 = source ∧
      memLoad callee.store (af.rsi + 16) 64 = destination ∧
      (memLoad callee.store (af.rsi + 24) 64).toNat = length.toNat / 16 ∧
      Writable code callee.store (fr.rsp - 120) 20 ∧ Readable callee.store source input.size ∧
      (span source input.size).HasBytes callee.store input ∧ Writable code callee.store destination input.size ∧
      (source = destination ∨ (span source input.size).Disjoint (span destination input.size)) ∧
      (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
        (span destination input.size).Disjoint (span slot 8) ∧
        (span (fr.rsp - 120) 20).Disjoint (span slot 8)) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)), span (fr.rsp - 120) 20,
        span source input.size, span destination input.size], (callStack af).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)), span (fr.rsp - 120) 20],
        (span destination input.size).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)),
        span source input.size, span destination input.size],
        (span (fr.rsp - 120) 20).Disjoint region) := by
    refine ⟨?_, ?_, hschedule', hrSchedule.of_frame hfSetup, ?_, ?_, ?_, ?_, ?_, ?_,
      hread.of_frame hfSetup, hbytes', hwrite.of_frame hfSetup, halias, ?_, ?_, ?_, ?_⟩
    · rw [akey]; exact localRead 128 8 (by omega) (by decide)
    · simpa only [akey] using hkey
    · rw [adesc]; exact localRead 200 32 (by omega) (by decide)
    · simpa only [adesc] using loads.2.1
    · rw [adesc, show fr.rsp - 200 + 8 = fr.rsp - 192 by bv_omega]; exact loads.2.2.1
    · rw [adesc, show fr.rsp - 200 + 16 = fr.rsp - 184 by bv_omega]; exact loads.2.2.2.1
    · rw [adesc, show fr.rsp - 200 + 24 = fr.rsp - 176 by bv_omega, loads.2.2.2.2]
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · exact localWrite 120 20 (by omega) (by decide)
    · intro slot hin
      refine ⟨(hslotSep slot ?_).1, counterSlot slot ?_ ?_⟩
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hin ⊢
      all_goals rcases hin with rfl | rfl | rfl <;> decide
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, akey, adesc] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact stackApartLocal 128 8 (by omega) (by decide) (by decide)
      · exact stackApartLocal 200 32 (by omega) (by decide) (by decide)
      · exact stackApartExternal (hstackSep _ (by simp))
      · exact stackApartLocal 120 20 (by omega) (by decide) (by decide)
      · exact stackApartExternal (hstackSep _ (by simp))
      · exact stackApartExternal (hstackSep _ (by simp))
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, akey, adesc] at hin
      rcases hin with rfl | rfl | rfl | rfl
      · intro x hx hy
        exact localApartExternal 128 8 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
      · intro x hx hy
        exact localApartExternal 200 32 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
      · exact hdataSep
      · intro x hx hy
        exact localApartExternal 120 20 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, akey, adesc] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl
      · exact localApart 120 20 128 8 (by omega) (by omega) (by decide) (by decide) (by decide)
      · exact localApart 120 20 200 32 (by omega) (by omega) (by decide) (by decide) (by decide)
      · exact localApartExternal 120 20 (by omega) (by decide) (hstackSep _ (by simp))
      · exact localApartExternal 120 20 (by omega) (by decide) (hstackSep _ (by simp))
      · exact localApartExternal 120 20 (by omega) (by decide) (hstackSep _ (by simp))
  have c39' : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ := (keep 39 (by decide)).trans h39
  have c50' : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ := (keep 50 (by decide)).trans h50
  have c51' : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ := (keep 51 (by decide)).trans h51
  have cw : (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).window = ctrWindow := by
    cases use256 <;> rfl
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l1084e0 else .l107050)
      (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo)
      (fun _ ↦ [span ((fr.rsp - 120) + 16) 4, span destination input.size]) _ _
      (crypt input (length.toNat / 16) hsize (fr.rdi + 32)
        (fr.rsp - 120) source destination)
      callee.store callee.arguments (if use256 then 0x1028d0 else 0x102470) lower
      (typed hTypes) (by rw [c39']; rfl) (by rw [c50']; rfl) (by rw [c51']; rfl)
      ((keep 22 (by decide)).trans h22)
      (by change Readable callee.store af.rsp 8; rw [asp]; exact localRead 224 8 (by omega) (by decide))
      (by change memLoad callee.store af.rsp 64 = _; rw [asp]; exact loads.1)
      (by cases use256 <;> decide)
      (by
        intro _
        rw [cw]
        change Writable code callee.store (af.rsp - BitVec.ofNat 64 ctrWindow) ctrWindow
        rw [asp, BitVec.sub_sub]
        have heq : (224 : BitVec 64) + BitVec.ofNat 64 ctrWindow = BitVec.ofNat 64 window := by
          change BitVec.ofNat 64 224 + _ = _
          rw [← BitVec.ofNat_add, hwsize]
        rw [heq]
        have hw : Writable code callee.store (fr.rsp - BitVec.ofNat 64 window) window := hstack.of_frame hfSetup
        exact hw.sub (Nat.le_refl _) (by omega))
      (by rw [cw]; change lower.toNat + ctrWindow ≤ af.rsp.toNat; rw [asp,ahigh,n224]; omega)
      (by change af.rsp.toNat % 16 = 8; rw [asp,n224]; omega) hslots hpre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store
    [af.region, span ((fr.rsp - 120) + 16) 4, span destination input.size] at hframe
  change memLoad output.store ((fr.rsp - 120) + 16) 32 =
      memLoad callee.store ((fr.rsp - 120) + 16) 32 + BitVec.ofNat 32 (length.toNat / 16) ∧ _ at hpost
  have inputPositive : 0 < input.size := by omega
  have counterAddress : (fr.rsp - 120) + 16 = fr.rsp - 104 := by bv_omega
  have counterSame : CTR.initialCounterBlock callee.store (fr.rsp - 120) =
      CTR.initialCounterBlock mem (fr.rsp - 120) := CTR.initialCounterBlock_of_frame hfSetup
    (setupLocal 120 20 (by decide) (by decide) (by decide))
  have counterLoad : memLoad callee.store (fr.rsp - 104) 32 = memLoad mem (fr.rsp - 104) 32 :=
    hfSetup.memLoad_eq (setupLocal 104 4 (by decide) (by decide) (by decide))
  dsimp only [activationOfValues] at hpost
  rw [counterAddress,counterLoad,counterSame] at hpost
  have hdone' : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  rcases hdone' with ⟨o4,o22,o3,o5,o12,o13,o14,o15,o39,o50,o51,_⟩
  let writes := [span lower (window - 100),span (fr.r8 + 8) 8,span destination input.size]
  have setupWithin : RegionsWithin setupRegions writes := by
    intro r hin
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower (window - 100),by simp [writes],?_,?_⟩ <;>
        simp only [span,ahigh,n224] <;> omega
    · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  have childWithin : RegionsWithin [af.region,span ((fr.rsp - 120) + 16) 4,span destination input.size] writes := by
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl
    · refine ⟨span lower (window - 100),by simp [writes],?_,?_⟩ <;>
        simp only [span,Activation.region,alow,asp,ahigh,n224] <;> omega
    · refine ⟨span lower (window - 100),by simp [writes],?_,?_⟩ <;>
        simp only [span,counterAddress,n104,ahigh] <;> omega
    · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  have hf := ((RamWriteFrame.refl _ _).trans hfSetup setupWithin).trans hframe childWithin
  have childLocal (off count : Nat) (hc : count ≤ off) (hpos : 0 < count)
      (hhi : off ≤ 216) (hlo : 104 + count ≤ off ∨ off + 4 ≤ 104) :
      Outside [af.region,span ((fr.rsp - 120) + 16) 4,span destination input.size]
        (fr.rsp - BitVec.ofNat 64 off) count := by
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega,?_⟩
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl
    · simp only [Activation.region,alow,asp,ahigh,n224,hsub off (by omega)]; omega
    · simp only [span,counterAddress,n104,hsub off (by omega)]; omega
    · have sep := disjoint_bounds _ _ _ _ hpos inputPositive
        (local_span_disjoint_external hroom (by omega : off ≤ window) hc
          (hstackSep (span destination input.size) (by simp)))
      exact sep
  have counterPrefix (n : Nat) (hn : n + 4 ≤ 16) :
      memLoad output.store ((fr.rsp - 120) + BitVec.ofNat 64 n) 32 =
        memLoad mem ((fr.rsp - 120) + BitVec.ofNat 64 n) 32 :=
    (hframe.memLoad_eq (outside_subregion
      (childLocal 120 16 (by decide) (by decide) (by decide) (by decide)) (by omega) hn)).trans
      (hfSetup.memLoad_eq (outside_subregion
        (setupLocal 120 16 (by decide) (by decide) (by decide)) (by omega) hn))
  have advanced := CTR.initialCounterBlock_advance mem output.store (fr.rsp - 120)
    (length.toNat / 16) (fun k ↦ counterPrefix (4 * k.val) (by have := k.isLt; omega))
    (counterPrefix 12 (by decide)) (by rw [counterAddress]; exact hpost.1)
  have retainedLocal (off : Nat) (hlo : 128 ≤ off) (hhi : off ≤ 168) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 :=
    (hframe.memLoad_eq (childLocal off 8 (by omega) (by decide) (by omega) (by omega))).trans
      (hfSetup.memLoad_eq (setupLocal off 8 (by omega) (by decide) hhi))
  have preservedKey : memLoad output.store (fr.rsp - 128) 64 = fr.rdi + 32 :=
    (retainedLocal 128 (by decide) (by decide)).trans hkeyPtr
  have savedOutside (off : Nat) (hoff : off ≤ 48) :
      Outside writes (fr.rsp - BitVec.ofNat 64 off) 8 := by
    refine ⟨by rw [hsub off (by omega)]; have := hretRead.low; omega,?_⟩
    intro r hin
    simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl
    · simp only [span,ahigh,hsub off (by omega)]; omega
    · have sep := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        (fr.r8 + 8).toNat 8 (by omega) (by decide) (hstackSep (span (fr.r8 + 8) 8) (by simp))
      simp only [span,hsub off (by omega)]
      omega
    · have sep := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        destination.toNat input.size (by omega) inputPositive (hstackSep (span destination input.size) (by simp))
      simp only [span,hsub off (by omega)]
      omega
  have delta : ((args[3].get 64 + ((16 : Nat) : BitVec 64)) &&& args[14].get 64) =
      BitVec.ofNat 64 input.size := by
    rw [hmask,hlen,hsize]
    exact length_full_block_mask length hbound
  have descriptorSetup : memLoad callee.store (fr.r8 + 8) 64 = destination + BitVec.ofNat 64 input.size := by
    have hfS := fullCtrMemory_stack_frame use256 args mem
      (by rw [hsp]; omega) (by rw [hsp]; have := hretRead.low; omega)
    have out : Outside [span (args[4].get 64 - 8) 56] (fr.r8 + 8) 8 := by
      refine ⟨Nat.le_trans hdescWrite.readable.low (by decide),?_⟩
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      have sep := disjoint_bounds _ _ _ _ (by decide : 0 < 56) (by decide : 0 < 8)
        (local_span_disjoint_external hroom (by omega : 224 ≤ window) (by decide : 56 ≤ 224)
          (hstackSep (span (fr.r8 + 8) 8) (by simp)))
      rw [a224]
      exact sep.symm
    rw [hm,hfS.memLoad_eq out,hdescriptor]
    rw [memLoad_memStore_same _ _ _ (by decide) (by decide),hdescDestination,delta,BitVec.add_comm]
  have descriptorResult : memLoad output.store (fr.r8 + 8) 64 = destination + BitVec.ofNat 64 input.size := by
    apply Eq.trans (hframe.memLoad_eq _) descriptorSetup
    refine ⟨Nat.le_trans hdescWrite.readable.low (by decide),?_⟩
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl
    · have sep := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        (fr.r8 + 8).toNat 8 (by omega) (by decide) (hstackSep (span (fr.r8 + 8) 8) (by simp))
      simp only [Activation.region,alow,asp,ahigh,n224]
      omega
    · have sep := disjoint_bounds _ _ _ _ (by decide : 0 < 4) (by decide : 0 < 8)
        (local_span_disjoint_external hroom (by omega : 104 ≤ window) (by decide : 4 ≤ 104)
          (hstackSep (span (fr.r8 + 8) 8) (by simp)))
      rw [counterAddress]
      exact sep.symm
    · exact disjoint_bounds _ _ _ _ (by decide : 0 < 8) inputPositive (hdescSep _ (by simp))
  have slotsOutside (ptr : BitVec 64) (hlo : 0x201208 ≤ ptr.toNat)
      (hhi : ptr.toNat + 8 ≤ 0x201238)
      (hin : ptr ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64))) : Outside writes ptr 8 := by
    refine ⟨by omega,?_⟩
    intro r hr
    simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [span,ahigh]; omega
    · exact (disjoint_bounds _ _ _ _ (by decide : 0 < 8) (by decide : 0 < 8) (hslotSep ptr hin).2).symm
    · exact (disjoint_bounds _ _ _ _ inputPositive (by decide : 0 < 8) (hslotSep ptr hin).1).symm
  have savedLoad (off : Nat) (hoff : off ≤ 48) := hf.memLoad_eq (k := 64) (savedOutside off hoff)
  have savedReturn : memLoad output.store fr.rsp 64 = fr.ret := by
    have he := savedLoad 0 (by decide)
    simp only [BitVec.sub_zero] at he
    exact he.trans hret
  have af5 : af.rbp = fr.rcx := by
    change (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = _
    exact congrArg (Value.get 64) ((keep 5 (by decide)).trans h5)
  have af39 : af.mxcsr = fr.mxcsr := congrArg (Value.get 32) c39'
  have af50 : af.ftw = fr.ftw := congrArg (Value.get 16) c50'
  have af51 : af.fcw = fr.fcw := congrArg (Value.get 16) c51'
  have outsp : output.values[4] = ⟨64,fr.rsp - 216⟩ := by
    rw [o4,asp]
    congr 1
    bv_omega
  let next := cont.resume output
  have na : next.arguments = output.values := CFGCall.resume_arguments cont output
  have nm : next.store = output.store := rfl
  have nl : next.label = (if use256 then .l1028d0 else .l102470) := hc
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt .l1028d0 fr else LIR.Fn1022c0.frameAt .l102470 fr) := by
    rw [na,nm]
    cases use256 <;> exact ⟨outsp,o22,o5.trans (congrArg (Value.mk 64) af5),
      o39.trans (congrArg (Value.mk 32) af39),o50.trans (congrArg (Value.mk 16) af50),
      o51.trans (congrArg (Value.mk 16) af51),
      (retainedLocal 152 (by decide) (by decide)).trans descriptorLocal,
      (retainedLocal 136 (by decide) (by decide)).trans haadLocal,
      (savedLoad 48 (by decide)).trans hs3,(savedLoad 40 (by decide)).trans hs12,
      (savedLoad 32 (by decide)).trans hs13,(savedLoad 24 (by decide)).trans hs14,
      (savedLoad 16 (by decide)).trans hs15,(savedLoad 8 (by decide)).trans hs5,
      hretRead.of_frame hf,savedReturn,hretLow,hstack.of_frame hf,hroom,halign,
      hs0r.of_frame hf,(hf.memLoad_eq (slotsOutside _ (by decide) (by decide) (by simp))).trans hs0,
      hs1r.of_frame hf,(hf.memLoad_eq (slotsOutside _ (by decide) (by decide) (by simp))).trans hs1,
      hs2r.of_frame hf,(hf.memLoad_eq (slotsOutside _ (by decide) (by decide) (by simp))).trans hs2,
      hs3r.of_frame hf,(hf.memLoad_eq (slotsOutside _ (by decide) (by decide) (by simp))).trans hs3slot,
      hslotsSep,trivial⟩
  have ex : LIR.program.Exec (dialect code) ⟨callee,[]⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label,callee.arguments,callee.store⟩,[]⟩ output
    rw [hl]
    exact hexec
  have accepted : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts,hg,htag]
    cases use256 <;> rfl
  have step : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l102885 else .l102425),args,mem⟩,[]⟩ = .next ⟨callee,[cont]⟩ := by
    rw [Program.step,hx]; rfl
  refine ⟨next,(Semantics.Reaches.single step).trans (CFGCall.exec_reaches_resume ex cont [] accepted),
    nl,working,?_,hf,?_,?_,?_,?_,descriptorResult,hpost.1,advanced,hpost.2,preservedKey⟩
  · simpa only [na] using houtTypes
  · rw [na,o3]
    change ((callee.arguments[3]'(by change 3 < 53; decide)).get 64).setWidth 8 = args[0].get 8
    rw [c3]
    simp only [Value.get,BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  · rw [na,o13]
    change (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = _
    rw [c13]
    change args[12].get 64 + _ = _
    rw [hsource,delta]
  · rw [na,o14]
    change (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = _
    rw [c14]
    change (args[14].get 32 &&& 15).setWidth 64 = _
    have h32 : args[14].get 32 = length.setWidth 32 := by
      rw [← hlen]
      simp only [Value.get,BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
    rw [h32]
    exact length_tail_byte_mask length
  · rw [na,o15]
    change (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = _
    exact (congrArg (Value.get 64) (keep 15 (by decide))).trans hcounter
end AesGcm.Proofs.Machine.Core.Decrypt
