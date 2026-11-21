import AesGcm.Proofs.Machine.Core.Encrypt.CiphertextFrame
import AesGcm.Proofs.Machine.Core.Encrypt.Tail

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem tailFromFrame (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray)
    (source destination : BitVec 64) (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr))
    (hTypes : GPRsTyped args) (hsource : args[15].get 64 = source) (hdest : args[12].get 64 = destination)
    (hcount : (args[14].get 64).toNat = input.size) (hpositive : 0 < input.size) (hsize : input.size ≤ 16)
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rsi + 32) mem)
    (hscheduleRead : Readable mem (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)))
    (hschedulePtr : memLoad mem (fr.rsp - 152) 64 = fr.rsi + 32)
    (hr : Readable mem source input.size) (hbytes : (span source input.size).HasBytes mem input)
    (hdw : Writable code mem destination input.size)
    (hsep : ∀ r ∈ [span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size], (callStack fr).Disjoint r)
    (hslotsSep : ∀ slot ∈ ([0x201208, 0x201228] : List (BitVec 64)),
      (span destination input.size).Disjoint (span slot 8)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102abe else .l10265e, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102b3e else .l1026de) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      RamWriteFrame mem next.store (ciphertextRegions use256 fr destination input.size) ∧
      (span destination input.size).HasBytes next.store
        (AesGcm.Spec.GCM.byteArrayOfBits
          (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (fr.rsp - 144)))
            (AesGcm.Spec.GCM.bitsOfByteArray input))) := by
  let window : Nat := if use256 then 0xb50 else 0x940
  let ctrWindow : Nat := if use256 then 0xa80 else 0x870
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have facts : args[4] = ⟨64, fr.rsp - 200⟩ ∧ args[22] = ⟨1, 0⟩ ∧
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
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  obtain ⟨h4,h22,h39,h50,h51,_,_,_,_,_,_,_,_,_,_,hretRead,_,_,hw,hroom,halign,
    s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,hsa,_⟩ := facts
  have hwindow : window = 208 + ctrWindow := by cases use256 <;> decide
  have wmin : 200 ≤ window := by omega
  have hsub (n : Nat) (hn : n ≤ window) : (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    rw [BitVec.toNat_sub_of_le (by change n % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
  have hsp : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
  have hlower : (fr.rsp - BitVec.ofNat 64 window).toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have startEq : fr.rsp - 200 - BitVec.ofNat 64 (ctrWindow + 8) = fr.rsp - BitVec.ofNat 64 window := by
    rw [hwindow]
    cases use256 <;> simp only [ctrWindow, Bool.false_eq_true, ↓reduceIte] <;> bv_omega
  have tailWritable : Writable code mem
      (fr.rsp - 200 - BitVec.ofNat 64 (ctrWindow + 8)) (ctrWindow + 160) := by
    rw [startEq]
    apply hw.sub (Nat.le_refl _)
    change _ ≤ _
    omega
  have tailSep : ∀ r ∈ [span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size],
      (span (fr.rsp - 200 - BitVec.ofNat 64 (ctrWindow + 8)) (ctrWindow + 160)).Disjoint r := by
    intro r hr x hx hy
    apply hsep r hr x ?_ hy
    rw [startEq] at hx
    change (fr.rsp - BitVec.ofNat 64 window).toNat ≤ x ∧ x < (fr.rsp - BitVec.ofNat 64 window).toNat + (ctrWindow + 160) at hx
    rw [hlower] at hx
    change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
    omega
  obtain ⟨next, reach, label, types, keep, frame, bytes⟩ := tail use256 code hcode key input hsize hpositive
    args mem (fr.rsp - 200) (fr.rsi + 32) source destination
    (by rw [h4]; rfl) hsource hdest hcount (by rw [hsp]; omega) (by rw [hsp]; omega)
    tailWritable hschedule hscheduleRead
    (by simpa only [show fr.rsp - 200 + 48 = fr.rsp - 152 by bv_omega] using hschedulePtr)
    hr hbytes hdw tailSep ⟨s0r,s0v,s1r,s1v,s3r,s3v,s2r,s2v⟩
    (by rw [hsp]; cases use256 <;> simp only [ctrWindow, slotHigh, Bool.false_eq_true, ↓reduceIte] at * <;> omega)
    hTypes h22 (by rw [h39]; rfl) (by rw [h50]; rfl) (by rw [h51]; rfl)
  have frame' : RamWriteFrame mem next.store (ciphertextRegions use256 fr destination input.size) := by
    have first : ctrWindow + 96 = window - 112 := by omega
    change RamWriteFrame mem next.store [span (fr.rsp - 200 - BitVec.ofNat 64 (ctrWindow + 8)) (ctrWindow + 96), span (fr.rsp - 200 + 136) 16, span destination input.size] at frame
    change RamWriteFrame mem next.store [span (fr.rsp - BitVec.ofNat 64 window) (window - 112), span (fr.rsp - 64) 16, span destination input.size]
    simpa only [startEq, first,
      show fr.rsp - 200 + 136 = fr.rsp - 64 by bv_omega] using frame
  have keep' : ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = args[r] := by
    intro r hr
    apply keep r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  refine ⟨next, reach, label, authenticateFrame use256 code fr args next.arguments mem next.store destination input.size
      hworking frame' keep' hpositive hdw.readable (hsep _ (by simp)) hslotsSep, types, keep, frame', ?_⟩
  simpa only [show fr.rsp - 200 + 56 = fr.rsp - 144 by bv_omega] using bytes

end AesGcm.Proofs.Machine.Core.Encrypt
