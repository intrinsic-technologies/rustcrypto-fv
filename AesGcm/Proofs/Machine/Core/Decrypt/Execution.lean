import AesGcm.Proofs.Machine.Core.Decrypt.Payload
import AesGcm.Proofs.Machine.Core.Decrypt.Contract
import AesGcm.Proofs.Machine.Core.Decrypt.Entry
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.Core.Decrypt.Empty
import AesGcm.Proofs.Machine.Core.Decrypt.Authenticate
import AesGcm.Proofs.Machine.Tag.Semantics
import AesGcm.Proofs.Machine.Core.Decrypt.Tag
import AesGcm.Proofs.Machine.Core.Decrypt.Mask
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.Core.Decrypt.Native
import AesGcm.Proofs.Machine.Core.Decrypt.Branches
import AesGcm.Proofs.Machine.Core.Decrypt.Calls
import AesGcm.Proofs.Machine.Core.Decrypt.Authentication
import AesGcm.Proofs.Machine.Core.Decrypt.Finish
import AesGcm.Proofs.Machine.Core.Decrypt.FullBlocks
import AesGcm.Proofs.Machine.Core.Decrypt.Prefix
import AesGcm.Proofs.Machine.Core.Decrypt.Setup
import AesGcm.Proofs.Machine.Runtime.Result
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 750000 in
set_option maxRecDepth 4096 in
theorem decrypt_call_of_ctr (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16)
    (source destination : BitVec 64)
    (ctr : 0 < ciphertext.size →
      (AesGcm.Spec.GCM.authenticPlaintext (AES16.variant use256) key nonce
        associatedData ciphertext tag).isSome → CTR.CryptCall use256 code key) :
    DecryptCall use256 code key nonce associatedData ciphertext tag source destination := by
  intro fr loc hl hm he ht hp
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm he ht hp
  subst label mem
  change Values Value Reg.count at args
  have ef := entryFacts_of_atoms he
  rcases hp with ⟨hinput, hbuffer, hwdesc, hreadtag, htagbytes, hwdst,
    hslots, hsep, hdstsep, hdescsep⟩
  have hlow : fr.low.toNat ≤ fr.rsp.toNat := by
    have hr := ef.room
    cases use256 <;> simp only [LIR.Fn102720.frameInfo, LIR.Fn1022c0.frameInfo] at hr <;> omega
  have contextSep : (callStack fr).Disjoint
      (span fr.rdi (GcmContext.size (AES16.variant use256))) := hsep _ (by simp)
  have nonceSep : (callStack fr).Disjoint (span fr.rsi 12) := hsep _ (by simp)
  have aadSep : (callStack fr).Disjoint (span fr.rdx associatedData.size) := hsep _ (by simp)
  have descriptorSep : (callStack fr).Disjoint (span fr.r8 24) := hsep _ (by simp)
  have tagSep : (callStack fr).Disjoint (span fr.r9 16) := hsep _ (by simp)
  have sourceSep : (callStack fr).Disjoint (span source ciphertext.size) := hsep _ (by simp)
  have contextOut := outside_activationRegion hinput.2.1
    (by cases use256 <;> decide) hlow contextSep
  have nonceOut := outside_activationRegion hinput.2.2.1 (by decide) hlow nonceSep
  have descriptorOut := outside_activationRegion hbuffer.1 (by decide) hlow descriptorSep
  have tagOut := outside_activationRegion hreadtag (by decide) hlow tagSep
  have inputPreserved {after : Ram} (hf : RamWriteFrame fr.original after [fr.region]) :
      InputsIn use256 key nonce associatedData after fr.rdi fr.rsi fr.rdx fr.rcx :=
    hinput.of_frame_disjoint hf contextOut nonceOut (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact span_disjoint_activationRegion aadSep)
  have bufferPreserved {after : Ram} (hf : RamWriteFrame fr.original after [fr.region]) :
      BufferIn after fr.r8 source destination ciphertext :=
    hbuffer.of_frame_disjoint hf descriptorOut (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact span_disjoint_activationRegion sourceSep)
  have lengthBound : (memLoad fr.original (fr.r8 + 16) 64).toNat ≤ 2^32 := by
    have hc := hbuffer.2.2.2.1
    have hr := hbuffer.2.2.2.2.1.low
    omega
  have aadBound : fr.rcx.toNat ≤ 2^32 := by
    have hc := hinput.2.2.2.2.2.2
    have hr := hinput.2.2.2.2.1.low
    omega
  obtain ⟨entry, entryRun, entryLabel, entryFrame, entryTyped, entryWrites,
    entryLength, entryMask⟩ := Decrypt.entry use256 code hcode fr
      ⟨(if use256 then .l102720 else .l1022c0), args, fr.original⟩ rfl rfl he ht
      (memLoad fr.original (fr.r8 + 16) 64) lengthBound aadBound hbuffer.1 rfl descriptorSep
  have entryInput := inputPreserved entryWrites
  have scheduleSep : (callStack fr).Disjoint
      (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))) := by
    have hs := outside_subregion contextOut (offset := 32)
      (count := 16 * ((AES16.variant use256).Nr + 1))
      (by simp only [GcmContext.size]; omega) (by simp only [GcmContext.size]; omega)
    have hr := hinput.2.1.low
    have ha : (fr.rdi + 32).toNat = fr.rdi.toNat + 32 := by
      simp only [GcmContext.size] at hr
      bv_omega
    intro x hx hy
    apply contextSep x hx
    change (fr.rdi + 32).toNat ≤ x ∧
      x < (fr.rdi + 32).toNat + 16 * ((AES16.variant use256).Nr + 1) at hy
    change fr.rdi.toNat ≤ x ∧ x < fr.rdi.toNat + GcmContext.size (AES16.variant use256)
    rw [ha] at hy
    simp only [GcmContext.size]
    omega
  have scheduleRead : Readable entry.store (fr.rdi + 32)
      (16 * ((AES16.variant use256).Nr + 1)) := by
    apply entryInput.2.1.of_offsets (rfl : fr.rdi + 32 = fr.rdi + 32) (addr_self _)
    cases use256 <;> decide +kernel
  obtain ⟨mask, maskRun, maskLabel, maskFrame, maskTyped, maskWrites,
    maskRegister, maskLength, maskBlock, nonce0, nonce1, nonce2, schedulePointer⟩ :=
    Decrypt.mask_reaches use256 code hcode key nonce fr entry.arguments entry.store
      entryFrame entryTyped entryInput.1.1 scheduleRead scheduleSep
      entryInput.2.2.1 entryInput.2.2.2.1 nonceSep
  have throughMask : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨(if use256 then .l102720 else .l1022c0), args, fr.original⟩, []⟩ ⟨mask, []⟩ := by
    apply entryRun.trans
    cases entry
    subst_vars
    exact maskRun
  have maskAllWrites : RamWriteFrame fr.original mask.store [fr.region] :=
    entryWrites.trans maskWrites (fun r hr ↦ ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have maskInput := inputPreserved maskAllWrites
  have maskBuffer := bufferPreserved maskAllWrites
  have maskLengthNat : ((mask.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = ciphertext.size := by
    rw [maskLength, entryLength]
    exact hbuffer.2.2.2.1
  have maskRegisterValue : mask.arguments[3]'(by change 3 < 53; decide) = ⟨64, 0xfffffffe0⟩ :=
    maskRegister.trans entryMask
  let window : Nat := if use256 then 2912 else 2384
  have hwsize : 224 ≤ window := by cases use256 <;> decide
  have hroom : fr.low.toNat + window ≤ fr.rsp.toNat := by
    cases use256 <;> exact ef.room
  have hsub (off : Nat) (ho : off ≤ window) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    rw [BitVec.toNat_sub_of_le (by change off % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
  have maskStack : Writable code mask.store (fr.rsp - BitVec.ofNat 64 window) window := by
    have hw := ef.window (by cases use256 <;> decide)
    cases use256 <;> exact hw.of_frame maskAllWrites
  have maskRead : Readable mask.store (fr.rsp - 96) 16 := by
    apply maskStack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  let h := Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0)
  let maskValue := Standards.NIST.AES.cipher (AES16.variant use256) key
    (nonce ++ #v[(0 : UInt8),0,0,1])
  let computedTag := Tag.authenticationTagFromMask h maskValue associatedData ciphertext
  have hmaskBytes := hasBytes_of_memoryBlock maskRead maskBlock
  have context32 : Readable mask.store fr.rdi 32 := by
    apply maskInput.2.1.of_offsets (addr_self _) (addr_self _)
    cases use256 <;> decide +kernel
  have contextSep32 : (callStack fr).Disjoint (span fr.rdi 32) := by
    intro x hx hy
    apply contextSep x hx
    change fr.rdi.toNat ≤ x ∧ x < fr.rdi.toNat + 32 at hy
    change fr.rdi.toNat ≤ x ∧ x < fr.rdi.toNat + GcmContext.size (AES16.variant use256)
    simp only [GcmContext.size]
    omega
  obtain ⟨tagged, tagRun, tagLabel, tagFrame, tagTyped, tagWrites,
    tagMaskRegister, tagLength, tagSource, tagBytes⟩ :=
    Decrypt.tag_reaches use256 code hcode h maskValue associatedData ciphertext
      source destination fr mask.arguments mask.store maskFrame maskTyped context32
      maskInput.1.2.1 maskInput.1.2.2.1 maskInput.1.2.2.2.1 maskInput.1.2.2.2.2
      hmaskBytes maskInput.2.2.2.2.1 maskInput.2.2.2.2.2.1 maskInput.2.2.2.2.2.2
      maskBuffer maskLengthNat contextSep32 aadSep descriptorSep sourceSep
  have throughTag : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨(if use256 then .l102720 else .l1022c0), args, fr.original⟩, []⟩ ⟨tagged, []⟩ := by
    apply throughMask.trans
    cases mask
    subst_vars
    exact tagRun
  have tagWritesFull : RamWriteFrame mask.store tagged.store [fr.region] := by
    apply (RamWriteFrame.refl _ _).trans tagWrites
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change _
      have low : (fr.rsp - BitVec.ofNat 64 (if use256 then 2912 else 2384)).toNat =
          fr.rsp.toNat - window := hsub window (Nat.le_refl _)
      refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
        simp only [span, Activation.region, low]
      · omega
      · change fr.rsp.toNat - window + (window - 208) ≤ _
        omega
    · have n152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by omega)
      refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
        simp only [span, Activation.region, n152] <;> omega
    · have n80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := hsub 80 (by omega)
      refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
        simp only [span, Activation.region, n80] <;> omega
  have tagAllWrites : RamWriteFrame fr.original tagged.store [fr.region] :=
    maskAllWrites.trans tagWritesFull (fun r hr ↦ ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have providedTag := hasBytes_of_frame tagAllWrites htagbytes tagOut.1 (outside_disjoint_span tagOut)
  obtain ⟨authenticated, authRun, authLabel, authFrame, authTyped, authWrites, authAL, authKeep⟩ :=
    Decrypt.authenticate_reaches use256 code hcode fr tagged.arguments tagged.store
      computedTag tag tagFrame tagTyped tagBytes (hreadtag.of_frame tagAllWrites) providedTag
  have throughAuthentication : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨(if use256 then .l102720 else .l1022c0), args, fr.original⟩, []⟩ ⟨authenticated, []⟩ := by
    apply throughTag.trans
    cases tagged
    subst_vars
    exact authRun
  have authenticationAllWrites : RamWriteFrame fr.original authenticated.store [fr.region] := by
    apply tagAllWrites.trans authWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have n200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, n200] <;> omega
  have lengths : AesGcm.Spec.GCM.lengthsSupported associatedData.size ciphertext.size = true := by
    have ha : associatedData.size ≤ 2^32 := by have hh := hinput.2.2.2.2.1.low; omega
    have hc : ciphertext.size ≤ 2^32 := by
      have he := hbuffer.2.2.2.1
      omega
    change (decide (8 * ciphertext.size ≤ 8 * (2^36 - 32)) &&
      decide (8 * associatedData.size ≤ 8 * (2^61 - 1))) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  have hkey : Standards.NIST.GCM.bitsOfBytes h =
      AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key (Standards.NIST.GCM.zeros 128) := by
    have hz : Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.zeros 128) =
        Vector.replicate 16 (0 : UInt8) := by decide +kernel
    simp only [AesGcm.Spec.GCM.forwardCipher, hz, h]
  have hmaskValue : Standards.NIST.GCM.bitsOfBytes maskValue =
      AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key
        (Standards.NIST.GCM.preCounterBlock (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes nonce)) := by
    rw [← Tag.bitsOfBytes_nonce96_counter_one]
    simp only [AesGcm.Spec.GCM.forwardCipher, AesGcm.Proofs.bytesOfBits_bitsOfBytes, maskValue]
  have hspec := Tag.authenticPlaintext_eq_tag (AES16.variant use256) key nonce
    associatedData ciphertext tag h maskValue hkey hmaskValue
  simp only [lengths, ↓reduceIte] at hspec
  by_cases htagEq : computedTag = tag
  · have accepted : AesGcm.Spec.GCM.authenticPlaintext (AES16.variant use256) key nonce
        associatedData ciphertext tag = some (AesGcm.Spec.GCM.byteArrayOfBits
          (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.inc 32 (Standards.NIST.GCM.preCounterBlock
              (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
              (Standards.NIST.GCM.bitsOfBytes nonce))) (AesGcm.Spec.GCM.bitsOfByteArray ciphertext))) := by
      rw [hspec]
      exact ite_eq_left htagEq.symm
    have hlabel : authenticated.label = (if use256 then .l102849 else .l1023e9) := by
      simpa only [htagEq, ↓reduceIte] using authLabel
    rw [hlabel] at authFrame
    have authLength : ((authenticated.arguments[14]'(by change 14 < 53; decide)).get 64).toNat =
        ciphertext.size := by
      have k14 : authenticated.arguments[14]'(by change 14 < 53; decide) =
          tagged.arguments[14]'(by change 14 < 53; decide) := authKeep 14 (by decide)
      rw [k14,tagLength]
      exact maskLengthNat
    by_cases empty : ciphertext.size = 0
    · have zero : (authenticated.arguments[14]'(by change 14 < 53; decide)).get 64 = 0 := by
        apply BitVec.eq_of_toNat_eq
        change ((authenticated.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = 0
        rw [authLength,empty]
      have successFrame : Atom.All code authenticated.arguments authenticated.store
          (if use256 then LIR.Fn102720.frameAt .l102849 fr else LIR.Fn1022c0.frameAt .l1023e9 fr) := by
        cases use256 <;> exact authFrame
      obtain ⟨output,exec,ret,done,typed,writes,al⟩ := Decrypt.empty_exec use256 code hcode fr
        authenticated.arguments authenticated.store successFrame authTyped zero
      have allWrites : RamWriteFrame fr.original output.store [fr.region] := by
        apply authenticationAllWrites.trans writes
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        have n128 : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := hsub 128 (by omega)
        refine ⟨fr.region,by simp,?_,?_⟩ <;>
          simp only [span,Activation.region,n128] <;> omega
      have execution : LIR.program.Exec (dialect code)
          ⟨⟨(if use256 then .l102720 else .l1022c0),args,fr.original⟩,[]⟩ output := by
        apply Program.Exec.of_sem
        apply throughAuthentication.exec
        change (LIR.program.sem (dialect code)).Exec
          ⟨⟨authenticated.label,authenticated.arguments,authenticated.store⟩,[]⟩ output
        rw [hlabel]
        exact exec.sem
      refine ⟨output,execution,ret,done,typed,?_,?_⟩
      · apply (RamWriteFrame.refl _ _).trans allWrites
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨fr.region,by simp,Nat.le_refl _,Nat.le_refl _⟩
      · rw [accepted]
        refine ⟨?_,?_,?_⟩
        · rw [al]
          simpa only [htagEq,↓reduceIte] using authAL
        · refine ⟨?_,?_⟩
          · exact AesGcm.Proofs.byteArrayOfBits_size _
          · intro i
            have hi : i.val < ciphertext.size := by
              simpa only [AesGcm.Proofs.byteArrayOfBits_size] using i.isLt
            omega
        · have desc : memLoad output.store (fr.r8 + 8) 64 = memLoad fr.original (fr.r8 + 8) 64 :=
            allWrites.memLoad_eq (outside_subregion (offset := 8) (count := 8) descriptorOut (by decide) (by decide))
          rw [desc,hbuffer.2.2.1,empty]
          simp
    · have successFrame : Atom.All code authenticated.arguments authenticated.store
          (if use256 then LIR.Fn102720.frameAt .l102849 fr else LIR.Fn1022c0.frameAt .l1023e9 fr) := by
        cases use256 <;> exact authFrame
      obtain ⟨counter,cRun,cLabel,cFrame,cTyped,cWrites,cKeep,c15,cWords⟩ :=
        Decrypt.counter_reaches use256 code hcode fr authenticated.arguments authenticated.store
          successFrame authTyped
      have throughCounter : (LIR.program.sem (dialect code)).Reaches
          ⟨⟨(if use256 then .l102720 else .l1022c0),args,fr.original⟩,[]⟩ ⟨counter,[]⟩ := by
        apply throughAuthentication.trans
        change (LIR.program.sem (dialect code)).Reaches
          ⟨⟨authenticated.label,authenticated.arguments,authenticated.store⟩,[]⟩ ⟨counter,[]⟩
        rw [hlabel]
        exact cRun
      have rspLow : fr.rsp.toNat ≤ 2^32 := by
        have hh := maskStack.readable.low
        change (fr.rsp - BitVec.ofNat 64 window).toNat + window ≤ 2^32 at hh
        rw [hsub window (Nat.le_refl _)] at hh
        omega
      have n200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
      have n152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by omega)
      have n80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := hsub 80 (by omega)
      have nwin : (fr.rsp - BitVec.ofNat 64 (if use256 then 2912 else 2384)).toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
      have savedWord (n bits : Nat) (hn : n ≤ 199) (hc : 80 + bits / 8 ≤ n)
          (hd : n ≤ 144 ∨ 152 + bits / 8 ≤ n) :
          memLoad authenticated.store (fr.rsp - BitVec.ofNat 64 n) bits =
            memLoad mask.store (fr.rsp - BitVec.ofNat 64 n) bits := by
        apply Eq.trans (authWrites.memLoad_eq _) (tagWrites.memLoad_eq _)
        · refine ⟨by rw [hsub n (by omega)]; omega,?_⟩
          intro r hin
          obtain rfl := List.mem_singleton.mp hin
          simp only [span,hsub n (by omega),n200]
          omega
        · refine ⟨by rw [hsub n (by omega)]; omega,?_⟩
          intro r hin
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
          rcases hin with rfl | rfl | rfl
          · change _
            simp only [span,hsub n (by omega),nwin]
            omega
          · simp only [span,hsub n (by omega),n152]
            omega
          · simp only [span,hsub n (by omega),n80]
            omega
      rcases cWords with ⟨counterKey,counterNonce0,counterNonce1,counterNonce2,counterOne,counterCount⟩
      have counterKeyValue : memLoad counter.store (fr.rsp - 128) 64 = fr.rdi + 32 :=
        counterKey.trans ((savedWord 144 64 (by decide) (by decide) (by decide)).trans schedulePointer)
      have initialCounter : Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock counter.store (fr.rsp - 120)) =
          Standards.NIST.GCM.inc 32 (Standards.NIST.GCM.preCounterBlock
            (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.bitsOfBytes nonce)) := by
        apply CTR.initialCounterBlock_nonce96 entry.store counter.store fr.rsi (fr.rsp - 120)
          (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key) nonce entryInput.2.2.2.1
        · rintro ⟨k,hk⟩
          have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
          rcases cases with rfl | rfl | rfl
          · simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using
              counterNonce0.trans ((savedWord 156 32 (by decide) (by decide) (by decide)).trans nonce0)
          · change memLoad counter.store (fr.rsp - 120 + 4) 32 = memLoad entry.store (fr.rsi + 4) 32
            rw [show fr.rsp - 120 + 4 = fr.rsp - 116 by bv_omega]
            exact counterNonce1.trans ((savedWord 160 32 (by decide) (by decide) (by decide)).trans nonce1)
          · change memLoad counter.store (fr.rsp - 120 + 8) 32 = memLoad entry.store (fr.rsi + 8) 32
            rw [show fr.rsp - 120 + 8 = fr.rsp - 112 by bv_omega]
            exact counterNonce2.trans ((savedWord 164 32 (by decide) (by decide) (by decide)).trans nonce2)
        · simpa only [show fr.rsp - 120 + 12 = fr.rsp - 108 by bv_omega] using counterOne
        · simpa only [show fr.rsp - 120 + 16 = fr.rsp - 104 by bv_omega] using counterCount
      have counterAllWrites : RamWriteFrame fr.original counter.store [fr.region] := by
        apply authenticationAllWrites.trans cWrites
        intro r hin
        obtain rfl := List.mem_singleton.mp hin
        have n128 : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := hsub 128 (by omega)
        refine ⟨fr.region,by simp,?_,?_⟩ <;> simp only [span,Activation.region,n128] <;> omega
      have counterInput := inputPreserved counterAllWrites
      have counterBuffer := bufferPreserved counterAllWrites
      have cLength : ((counter.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = ciphertext.size := by
        exact (congrArg (fun v : Value ↦ (v.get 64).toNat) (cKeep 14 (by decide))).trans authLength
      have cSource : (counter.arguments[12]'(by change 12 < 53; decide)).get 64 = source := by
        exact congrArg (Value.get 64) ((cKeep 12 (by decide)).trans ((authKeep 12 (by decide)).trans tagSource))
      have cMask : (counter.arguments[3]'(by change 3 < 53; decide)).get 64 = 0xfffffffe0 := by
        exact congrArg (Value.get 64) ((cKeep 3 (by decide)).trans ((authKeep 3 (by decide)).trans (tagMaskRegister.trans maskRegisterValue)))
      have cCounter : (counter.arguments[15]'(by change 15 < 53; decide)).get 64 = fr.rsp - 120 := congrArg (Value.get 64) c15
      have cAL : (counter.arguments[0]'(by change 0 < 53; decide)).get 8 = 0 := by
        exact (congrArg (Value.get 8) (cKeep 0 (by decide))).trans (authAL.trans (ite_eq_left htagEq))
      have scheduleReadCounter : Readable counter.store (fr.rdi + 32)
          (16 * ((AES16.variant use256).Nr + 1)) := by
        apply counterInput.2.1.of_offsets (rfl : fr.rdi + 32 = fr.rdi + 32) (addr_self _)
        cases use256 <;> decide +kernel
      have positive : 0 < ciphertext.size := Nat.pos_of_ne_zero empty
      have crypt := ctr positive (by rw [accepted]; rfl)
      have destWriteCounter := (hwdst positive).of_frame counterAllWrites
      have descriptorWrite : Writable code counter.store (fr.r8 + 8) 8 := by
        have off : (fr.r8 + 8).toNat = fr.r8.toNat + 8 := by have hh := hwdesc.readable.low; bv_omega
        apply (hwdesc.of_frame counterAllWrites).sub <;> rw [off] <;> omega
      have scheduleContains {x : Nat} (hx : (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))).Contains x) :
          (span fr.rdi (GcmContext.size (AES16.variant use256))).Contains x := by
        have off : (fr.rdi + 32).toNat = fr.rdi.toNat + 32 := by
          have hh := hinput.2.1.low
          simp only [GcmContext.size] at hh
          bv_omega
        simp only [span, MemoryRegion.Contains, off, GcmContext.size] at hx ⊢
        omega
      rw [authLength] at cLabel
      obtain ⟨last, payloadRun, label, working, typed, payloadWrites, payloadAL, bytes, descriptor⟩ :=
        Decrypt.payload_reaches use256 code hcode key crypt fr counter source destination ciphertext positive
          cLabel cFrame cTyped cLength cSource cMask cCounter counterKeyValue counterBuffer counterInput.1.1
          scheduleReadCounter destWriteCounter descriptorWrite
          (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact scheduleSep
            · exact sourceSep
            · exact hsep _ (by simp)
            · exact descriptorSep)
          (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact fun x hx hy => hdescsep _ (by simp) x hx (scheduleContains hy)
            · exact hdescsep _ (by simp)
            · exact hdescsep _ (by simp))
          (fun x hx hy => hdstsep _ (by simp) x hx (scheduleContains hy)) hslots
      have reaches := throughCounter.trans payloadRun
      have al := payloadAL.trans cAL
      rw [initialCounter] at bytes
      have beforeWrites : RamWriteFrame fr.original counter.store
          [fr.region, span destination ciphertext.size, span (fr.r8 + 8) 8] := by
        apply (RamWriteFrame.refl _ _).trans counterAllWrites
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
      have writes := beforeWrites.trans payloadWrites (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
      have facts : last.arguments[4]'(by change 4 < 53; decide) = ⟨64,fr.rsp - 216⟩ ∧
          last.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ ∧
          last.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ ∧
          last.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ ∧
          last.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ ∧
          memLoad last.store (fr.rsp - 48) 64 = fr.rbx ∧
          memLoad last.store (fr.rsp - 40) 64 = fr.r12 ∧
          memLoad last.store (fr.rsp - 32) 64 = fr.r13 ∧
          memLoad last.store (fr.rsp - 24) 64 = fr.r14 ∧
          memLoad last.store (fr.rsp - 16) 64 = fr.r15 ∧
          memLoad last.store (fr.rsp - 8) 64 = fr.rbp ∧
          Readable last.store fr.rsp 8 ∧ memLoad last.store fr.rsp 64 = fr.ret ∧
          fr.ret.toNat < 2^32 ∧ Writable code last.store (fr.rsp - BitVec.ofNat 64 window) window ∧
          fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True := by
        cases use256 <;> exact working
      rcases facts with ⟨a4,a22,a39,a50,a51,s3,s12,s13,s14,s15,s5,hr,hret,hrl,hw,room,align,_⟩
      have sp : (last.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 216 := congrArg (Value.get 64) a4
      have readable : Readable last.store ((last.arguments[4]'(by change 4 < 53; decide)).get 64 + 168) 56 := by
        have address : (last.arguments[4]'(by change 4 < 53; decide)).get 64 + 168 = fr.rsp - 48 := by rw [sp]; bv_omega
        rw [address]
        apply readable_append (n := 48) (k := 8)
        · apply hw.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
          cases use256 <;> decide +kernel
        · change Readable last.store (fr.rsp - 48 + 48) 8
          rw [BitVec.sub_add_cancel]
          exact hr
      obtain ⟨output,exec,ret,done,ot,memory,rax⟩ := Decrypt.finish_exec use256 code fr
        last.arguments last.store typed sp readable hret hrl s3 s12 s13 s14 s15 s5 a22 a39 a50 a51
      have execution : LIR.program.Exec (dialect code)
          ⟨⟨(if use256 then .l102720 else .l1022c0),args,fr.original⟩,[]⟩ output := by
        apply Program.Exec.of_sem
        apply reaches.exec
        change (LIR.program.sem (dialect code)).Exec ⟨⟨last.label,last.arguments,last.store⟩,[]⟩ output
        rw [label]
        exact exec.sem
      refine ⟨output,execution,ret,done,ot,?_,?_⟩
      · rw [memory]
        exact writes
      · rw [accepted]
        refine ⟨?_,?_,?_⟩
        · exact (congrArg (Value.get 8) rax).trans al
        · rw [memory]
          exact bytes
        · rw [memory]
          exact descriptor
  · have rejected : AesGcm.Spec.GCM.authenticPlaintext (AES16.variant use256) key nonce
        associatedData ciphertext tag = none := by
      rw [hspec]
      exact ite_eq_right (Ne.symm htagEq)
    have hlabel : authenticated.label = (if use256 then .l102961 else .l102501) := by
      simpa only [htagEq, ↓reduceIte] using authLabel
    rw [hlabel] at authFrame
    have aframe : authenticated.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 216⟩ ∧
        authenticated.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ ∧
        authenticated.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ ∧
        authenticated.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ ∧
        authenticated.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ ∧
        memLoad authenticated.store (fr.rsp - 48) 64 = fr.rbx ∧
        memLoad authenticated.store (fr.rsp - 40) 64 = fr.r12 ∧
        memLoad authenticated.store (fr.rsp - 32) 64 = fr.r13 ∧
        memLoad authenticated.store (fr.rsp - 24) 64 = fr.r14 ∧
        memLoad authenticated.store (fr.rsp - 16) 64 = fr.r15 ∧
        memLoad authenticated.store (fr.rsp - 8) 64 = fr.rbp ∧
        Readable authenticated.store fr.rsp 8 ∧ memLoad authenticated.store fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧ Writable code authenticated.store (fr.rsp - BitVec.ofNat 64 window) window ∧
        fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True := by
      cases use256 <;> exact authFrame
    obtain ⟨a4,a22,a39,a50,a51,a3,a12,a13,a14,a15,a5,ar,aret,aretLow,aw,aroom,aalign,_⟩ := aframe
    have asp : (authenticated.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 216 := by rw [a4]; rfl
    have arSaved : Readable authenticated.store ((authenticated.arguments[4]'(by change 4 < 53; decide)).get 64 + 168) 56 := by
      have ap : (authenticated.arguments[4]'(by change 4 < 53; decide)).get 64 + 168 = fr.rsp - 48 := by rw [asp]; bv_omega
      rw [ap]
      apply readable_append (n := 48) (k := 8)
      · apply aw.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
        cases use256 <;> decide +kernel
      · change Readable authenticated.store (fr.rsp - 48 + 48) 8
        rw [BitVec.sub_add_cancel]
        exact ar
    obtain ⟨output, exec, ret, done, typed, memory, rax⟩ := Decrypt.finish_exec use256 code fr
      authenticated.arguments authenticated.store authTyped asp arSaved aret aretLow
      a3 a12 a13 a14 a15 a5 a22 a39 a50 a51
    have fullExec : LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l102720 else .l1022c0),args,fr.original⟩,[]⟩ output := by
      apply Program.Exec.of_sem
      apply throughAuthentication.exec
      change (LIR.program.sem (dialect code)).Exec
        ⟨⟨authenticated.label, authenticated.arguments, authenticated.store⟩,[]⟩ output
      rw [hlabel]
      exact exec.sem
    refine ⟨output,fullExec,ret,done,typed,?_,?_⟩
    · rw [memory]
      apply (RamWriteFrame.refl _ _).trans authenticationAllWrites
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · rw [rejected]
      refine ⟨?_,?_⟩
      · rw [rax]
        simpa only [htagEq, ↓reduceIte] using authAL
      · rw [memory]
        exact authenticationAllWrites

end AesGcm.Proofs.Machine.Core
