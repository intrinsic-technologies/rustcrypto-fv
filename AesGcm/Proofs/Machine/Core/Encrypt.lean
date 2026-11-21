import AesGcm.Proofs.Machine.Core.Encrypt.Prefix
import AesGcm.Proofs.Machine.Core.Encrypt.Mask
import AesGcm.Proofs.Machine.Core.Encrypt.CounterSetup
import AesGcm.Proofs.Machine.Core.Encrypt.TailFrame
import AesGcm.Proofs.Machine.Core.Encrypt.TailCTR
import AesGcm.Proofs.Machine.Core.Encrypt.TailCopy
import AesGcm.Proofs.Machine.Core.Encrypt.Padding
import AesGcm.Proofs.Machine.Core.Encrypt.FullBlocks
import AesGcm.Proofs.Machine.Core.Encrypt.Branches
import AesGcm.Proofs.Machine.Core.Encrypt.Authenticate
import AesGcm.Proofs.Machine.Core.Interface
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem encrypt_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (associatedData plaintext : ByteArray) (source destination : BitVec 64) :
    CallContract LIR.lifted code (if use256 then .l102980 else .l102520)
      (if use256 then LIR.Fn102980.frameInfo else LIR.Fn102520.frameInfo)
      (fun fr ↦ [span fr.rdi 17, span destination plaintext.size])
      (fun fr mem ↦
        InputsIn use256 key nonce associatedData mem fr.rsi fr.rdx fr.rcx fr.r8 ∧
        BufferIn mem fr.r9 source destination plaintext ∧
        (0 < plaintext.size → Writable code mem destination plaintext.size) ∧ Writable code mem fr.rdi 17 ∧
        (∀ slot ∈ ([0x201208, 0x201210, 0x201228, 0x201230] : List (BitVec 64)),
          (span destination plaintext.size).Disjoint (span slot 8)) ∧
        (∀ region ∈ [span fr.rsi (GcmContext.size (AES16.variant use256)),
          span fr.rdx 12, span fr.rcx associatedData.size, span fr.r9 24,
          span source plaintext.size, span destination plaintext.size, span fr.rdi 17],
          (callStack fr).Disjoint region) ∧
        (∀ region ∈ [span fr.rsi (GcmContext.size (AES16.variant use256)),
          span fr.rdx 12, span fr.rcx associatedData.size, span fr.r9 24],
          (span destination plaintext.size).Disjoint region) ∧
        (∀ region ∈ [span fr.rsi (GcmContext.size (AES16.variant use256)),
          span fr.rdx 12, span fr.rcx associatedData.size, span fr.r9 24,
          span source plaintext.size, span destination plaintext.size],
          (span fr.rdi 17).Disjoint region))
      (fun fr mem ↦ ∃ ciphertext tag,
        AesGcm.Spec.GCM.ciphertextAndTag (AES16.variant use256) key nonce associatedData plaintext =
          some (ciphertext, tag) ∧
        mem[fr.rdi]? = some 0 ∧
        (span destination plaintext.size).HasBytes mem ciphertext ∧
        (span (fr.rdi + 1) 16).HasBytes mem ⟨tag.toArray⟩) := by
  intro fr loc hl hm he ht hp
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm he ht hp
  subst label mem
  change Values Value Reg.count at args
  have ef := entryFacts_of_atoms he
  rcases hp with ⟨hinput, hbuffer, hwdst, hwresult, hslots, hsep, hdstsep, hresultsep⟩
  let window : Nat := if use256 then 0xb50 else 0x940
  have wmin : 208 ≤ window := by cases use256 <;> decide
  have room : fr.low.toNat + window ≤ fr.rsp.toNat := by cases use256 <;> exact ef.room
  have hlow : fr.low.toNat ≤ fr.rsp.toNat := by omega
  have sub64 : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 := stack_sub_toNat fr (n := 64) room (by omega)
  have sub80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := stack_sub_toNat fr (n := 80) room (by omega)
  have sub152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := stack_sub_toNat fr (n := 152) room (by omega)
  have lower : (fr.rsp - BitVec.ofNat 64 window).toNat = fr.rsp.toNat - window := stack_sub_toNat fr room (Nat.le_refl _)
  have contextSep : (callStack fr).Disjoint (span fr.rsi (GcmContext.size (AES16.variant use256))) := hsep _ (by simp)
  have nonceSep : (callStack fr).Disjoint (span fr.rdx 12) := hsep _ (by simp)
  have aadSep : (callStack fr).Disjoint (span fr.rcx associatedData.size) := hsep _ (by simp)
  have descriptorSep : (callStack fr).Disjoint (span fr.r9 24) := hsep _ (by simp)
  have sourceSep : (callStack fr).Disjoint (span source plaintext.size) := hsep _ (by simp)
  have destinationSep : (callStack fr).Disjoint (span destination plaintext.size) := hsep _ (by simp)
  have resultSep : (callStack fr).Disjoint (span fr.rdi 17) := hsep _ (by simp)
  have contextOut := outside_activationRegion hinput.2.1
    (by cases use256 <;> decide) hlow contextSep
  have nonceOut := outside_activationRegion hinput.2.2.1 (by decide) hlow nonceSep
  have descriptorOut := outside_activationRegion hbuffer.1 (by decide) hlow descriptorSep
  have inputPreserved {after : Ram} (hf : RamWriteFrame fr.original after [fr.region]) :
      InputsIn use256 key nonce associatedData after fr.rsi fr.rdx fr.rcx fr.r8 :=
    hinput.of_frame_disjoint hf contextOut nonceOut (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact span_disjoint_activationRegion aadSep)
  have bufferPreserved {after : Ram} (hf : RamWriteFrame fr.original after [fr.region]) :
      BufferIn after fr.r9 source destination plaintext :=
    hbuffer.of_frame_disjoint hf descriptorOut (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact span_disjoint_activationRegion sourceSep)
  have lengthBound : plaintext.size ≤ 2^32 := by
    have := hbuffer.2.2.2.2.1.low
    omega
  have aadBound : associatedData.size ≤ 2^32 := by
    have := hinput.2.2.2.2.1.low
    omega
  let length := memLoad fr.original (fr.r9 + 16) 64
  have lengthSize : length.toNat = plaintext.size := hbuffer.2.2.2.1
  obtain ⟨entered, entryRun, entryLabel, entryFrame, entryTyped, entryWrites, entryLength⟩ :=
    Encrypt.entry use256 code hcode fr
      ⟨(if use256 then .l102980 else .l102520), args, fr.original⟩ rfl rfl he ht
      length (by rw [lengthSize]; exact lengthBound)
      (by rw [hinput.2.2.2.2.2.2]; exact aadBound) hbuffer.1 rfl descriptorSep
  have entryInput := inputPreserved entryWrites
  obtain ⟨masked, maskRun, maskLabel, maskFrame, maskTyped, maskWrites,
    maskBlock, maskKey, maskLength, maskNonce0, maskNonce1, maskNonce2⟩ :=
    Encrypt.mask use256 code hcode key nonce fr entered entryLabel entryFrame entryTyped
      entryInput.1.1 entryInput.2.1 entryInput.2.2.1 entryInput.2.2.2.1 contextSep nonceSep
  have stackWithin : RegionsWithin [span (fr.rsp - BitVec.ofNat 64 window) window] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [span, Activation.region, lower] <;> omega
  have maskAllWrites : RamWriteFrame fr.original masked.store [fr.region] :=
    entryWrites.trans maskWrites stackWithin
  have maskBuffer := bufferPreserved maskAllWrites
  obtain ⟨counter, counterRun, counterLabel, counterFrame, counterTyped, counterWrites,
    counterMemory, counterPtr, counterLength, counterDestination, counterSource⟩ :=
    Encrypt.counter use256 code hcode fr masked source destination maskLabel maskFrame maskTyped
      maskBuffer.1 maskBuffer.2.1 maskBuffer.2.2.1 descriptorSep
  have counterAllWrites : RamWriteFrame fr.original counter.store [fr.region] := by
    apply maskAllWrites.trans counterWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, sub152] <;> omega
  have counterAllWritesFull : RamWriteFrame fr.original counter.store [fr.region, span destination plaintext.size] := by
    apply (RamWriteFrame.refl _ _).trans counterAllWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have counterLengthEq : (counter.arguments[5]'(by change 5 < 53; decide)).get 64 = length :=
    counterLength.trans (maskLength.trans entryLength)
  have counterLengthNat : ((counter.arguments[5]'(by change 5 < 53; decide)).get 64).toNat = plaintext.size := by
    rw [counterLengthEq, lengthSize]
  let cipher := AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key
  let initial := Standards.NIST.GCM.inc 32
    (Standards.NIST.GCM.preCounterBlock cipher (Standards.NIST.GCM.bitsOfBytes nonce))
  let ciphertext := AesGcm.Spec.GCM.byteArrayOfBits
    (Standards.NIST.GCM.GCTR cipher initial (AesGcm.Spec.GCM.bitsOfByteArray plaintext))
  have cipherSize : ciphertext.size = plaintext.size := AesGcm.Proofs.byteArrayOfBits_size _
  have maskedSP : (masked.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 200 := by
    have hh : masked.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 200⟩ := by
      cases use256 <;> exact maskFrame.1
    rw [hh]
    rfl
  have counterLoads := Encrypt.counterMemory_loads masked.arguments masked.store
  rw [← counterMemory, maskedSP] at counterLoads
  rcases counterLoads with ⟨keyLoad, nonceLoad0, nonceLoad1, nonceLoad2, counterOne, counterOffset⟩
  have inputAfter {after : Ram} (hf : RamWriteFrame fr.original after [fr.region, span destination plaintext.size]) :
      InputsIn use256 key nonce associatedData after fr.rsi fr.rdx fr.rcx fr.r8 := by
    by_cases pos : 0 < plaintext.size
    · have outsideData {base : BitVec 64} {count : Nat} (hp : 0 < count)
          (hr : Readable fr.original base count) (ho : Outside [fr.region] base count)
          (hd : (span destination plaintext.size).Disjoint (span base count)) :
          Outside [fr.region, span destination plaintext.size] base count := by
        refine ⟨ho.1, ?_⟩
        intro r hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl
        · exact ho.2 _ (by simp)
        · exact disjoint_bounds base.toNat count destination.toNat plaintext.size hp pos
            (fun x hx hy ↦ hd x hy hx)
      apply hinput.of_frame_disjoint hf
        (outsideData (by cases use256 <;> decide) hinput.2.1 contextOut (hdstsep _ (by simp)))
        (outsideData (by decide) hinput.2.2.1 nonceOut (hdstsep _ (by simp)))
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact span_disjoint_activationRegion aadSep
      · exact fun x hx hy ↦ hdstsep _ (by simp) x hy hx
    · have zero : plaintext.size = 0 := by omega
      have onlyStack : RamWriteFrame fr.original after [fr.region] := by
        refine ⟨?_, hf.present⟩
        intro a ha
        apply hf.outside a
        refine ⟨ha.1, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ha.2 _ (by simp)
        · simp only [span, zero]
          omega
      exact inputPreserved onlyStack
  have counterInitial : Standards.NIST.GCM.bitsOfBytes
      (CTR.initialCounterBlock counter.store (fr.rsp - 144)) = initial := by
    apply CTR.initialCounterBlock_nonce96 entered.store counter.store fr.rdx (fr.rsp - 144)
      cipher nonce entryInput.2.2.2.1
    · intro k
      have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
      rcases hcases with hk | hk | hk
      all_goals simp only [hk, Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Nat.reduceMul]
      · change memLoad counter.store (fr.rsp - 144) 32 = memLoad entered.store fr.rdx 32
        erw [show fr.rsp - 144 = fr.rsp - 200 + 56 by bv_omega, nonceLoad0,
          ← setWidth_get _ (by decide : 32 ≤ 64), maskNonce0, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      · change memLoad counter.store (fr.rsp - 144 + 4) 32 = memLoad entered.store (fr.rdx + 4) 32
        erw [show fr.rsp - 144 + 4 = fr.rsp - 200 + 60 by bv_omega, nonceLoad1,
          ← setWidth_get _ (by decide : 32 ≤ 64), maskNonce1, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      · change memLoad counter.store (fr.rsp - 144 + 8) 32 = memLoad entered.store (fr.rdx + 8) 32
        erw [show fr.rsp - 144 + 8 = fr.rsp - 200 + 64 by bv_omega, nonceLoad2,
          ← setWidth_get _ (by decide : 32 ≤ 64), maskNonce2, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    · simpa only [show fr.rsp - 200 + 68 = fr.rsp - 144 + 12 by bv_omega] using counterOne
    · simpa only [show fr.rsp - 200 + 72 = fr.rsp - 144 + 16 by bv_omega] using counterOffset
  have counterKey : memLoad counter.store (fr.rsp - 152) 64 = fr.rsi + 32 := by
    simpa only [show fr.rsp - 200 + 48 = fr.rsp - 152 by bv_omega] using keyLoad.trans maskKey
  let maskValue := Standards.NIST.AES.cipher (AES16.variant use256) key
    (nonce ++ #v[(0 : UInt8),0,0,1])
  have maskStack : Writable code masked.store (fr.rsp - BitVec.ofNat 64 window) window := by
    have hw := ef.window (by cases use256 <;> decide)
    cases use256 <;> exact hw.of_frame maskAllWrites
  have maskRead : Readable masked.store (fr.rsp - 80) 16 := by
    apply maskStack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have maskBytes := hasBytes_of_memoryBlock maskRead maskBlock
  have counterMask : (span (fr.rsp - 80) 16).HasBytes counter.store ⟨maskValue.toArray⟩ := by
    apply hasBytes_of_frame counterWrites maskBytes
    · simp only [span, sub80]
      have := ef.slot.low
      omega
    · intro r hr x hx hy
      obtain rfl := List.mem_singleton.mp hr
      simp only [MemoryRegion.Contains, span, sub80] at hx
      simp only [MemoryRegion.Contains, span, sub152] at hy
      omega
  have counterInput := inputPreserved counterAllWrites
  have counterBuffer := bufferPreserved counterAllWrites
  have scheduleRead : Readable counter.store (fr.rsi + 32)
      (16 * ((AES16.variant use256).Nr + 1)) := by
    apply counterInput.2.1.of_offsets (rfl : fr.rsi + 32 = fr.rsi + 32) (addr_self _)
    cases use256 <;> decide +kernel
  have scheduleSep : (callStack fr).Disjoint
      (span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1))) := by
    have hr := hinput.2.1.low
    have ha : (fr.rsi + 32).toNat = fr.rsi.toNat + 32 := by
      simp only [GcmContext.size] at hr
      bv_omega
    intro x hx hy
    apply contextSep x hx
    change (fr.rsi + 32).toNat ≤ x ∧
      x < (fr.rsi + 32).toNat + 16 * ((AES16.variant use256).Nr + 1) at hy
    change fr.rsi.toNat ≤ x ∧ x < fr.rsi.toNat + GcmContext.size (AES16.variant use256)
    rw [ha] at hy
    simp only [GcmContext.size]
    omega
  have scheduleDataSep : (span destination plaintext.size).Disjoint
      (span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1))) := by
    have hr := hinput.2.1.low
    have ha : (fr.rsi + 32).toNat = fr.rsi.toNat + 32 := by
      simp only [GcmContext.size] at hr
      bv_omega
    intro x hx hy
    apply hdstsep (span fr.rsi (GcmContext.size (AES16.variant use256))) (by simp) x hx
    change (fr.rsi + 32).toNat ≤ x ∧
      x < (fr.rsi + 32).toNat + 16 * ((AES16.variant use256).Nr + 1) at hy
    change fr.rsi.toNat ≤ x ∧ x < fr.rsi.toNat + GcmContext.size (AES16.variant use256)
    rw [ha] at hy
    simp only [GcmContext.size]
    omega
  have frameKeep (before after : Values Value Reg.count) (mem : Ram)
      (hf : Atom.All code before mem
        (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr))
      (hk : ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → after[r] = before[r]) :
      Atom.All code after mem
        (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
    cases use256
    all_goals exact ⟨(hk 4 (by decide)).trans hf.1, (hk 22 (by decide)).trans hf.2.1,
      (hk 39 (by decide)).trans hf.2.2.1, (hk 50 (by decide)).trans hf.2.2.2.1,
      (hk 51 (by decide)).trans hf.2.2.2.2.1, hf.2.2.2.2.2⟩
  have frameAuth (values : Values Value Reg.count) (mem : Ram)
      (hf : Atom.All code values mem
        (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr)) :
      Atom.All code values mem
        (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr) := by
    cases use256
    all_goals
      rcases hf with ⟨r4,r22,r39,r50,r51,m112,m104,m96,m88,m48,m40,m32,m24,m16,m8,
        rr,rv,rl,ww,room,align,s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,ss,_⟩
      refine ⟨r4,r22,r39,r50,r51,m112,m104,m96,m88,m48,m40,m32,m24,m16,m8,
        rr,rv,rl,ww,room,align,s0r,s0v,s2r,s2v,?_,trivial⟩
      change _ ∨ _ at ss ⊢
      omega
  have counterFrameFull : Atom.All code counter.arguments counter.store
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
    cases use256 <;> exact ⟨counterFrame.1,counterFrame.2.1,counterFrame.2.2.2⟩
  have shrinkKeep {before after : Values Value Reg.count} {rs : List Nat}
      (hk : ∀ r : Fin 53, r.val ∈ rs → after[r] = before[r])
      (hsub : ∀ r ∈ ([4,22,39,50,51] : List Nat), r ∈ rs) :
      ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → after[r] = before[r] :=
    fun r hr ↦ hk r (hsub _ hr)
  have getKeep {before after : Values Value Reg.count} {rs : List Nat}
      (hk : ∀ r : Fin 53, r.val ∈ rs → after[r] = before[r]) (r : Fin 53) (hr : r.val ∈ rs) :
      (after[r]).get 64 = (before[r]).get 64 := congrArg (fun v : Value ↦ v.get 64) (hk r hr)
  let blocks := if plaintext.size < 17 then 0 else plaintext.size / 16
  let frontSize := 16 * blocks
  let tailSize := plaintext.size - frontSize
  let front := plaintext.extract 0 frontSize
  let tail := plaintext.extract frontSize plaintext.size
  have frontLe : frontSize ≤ plaintext.size := by
    dsimp only [frontSize, blocks]
    split <;> omega
  have frontSizeEq : front.size = frontSize := by
    simp only [front, ByteArray.size_extract, Nat.min_eq_left frontLe, Nat.sub_zero]
  have tailSizeEq : tail.size = tailSize := by
    simp only [tail, tailSize, ByteArray.size_extract, Nat.min_self]
  have tailLe : tailSize ≤ 16 := by
    dsimp only [tailSize, frontSize, blocks]
    split <;> omega
  have splitPlaintext : front ++ tail = plaintext := by
    dsimp only [front, tail]
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega : 0 ≤ frontSize), Nat.max_eq_right frontLe, ByteArray.extract_zero_size]
  let frontCipher := AesGcm.Spec.GCM.byteArrayOfBits
    (Standards.NIST.GCM.GCTR cipher initial (AesGcm.Spec.GCM.bitsOfByteArray front))
  let tailCounter := Nat.repeat (Standards.NIST.GCM.inc 32) blocks initial
  let tailCipher := AesGcm.Spec.GCM.byteArrayOfBits
    (Standards.NIST.GCM.GCTR cipher tailCounter (AesGcm.Spec.GCM.bitsOfByteArray tail))
  have frontCipherSize : frontCipher.size = frontSize :=
    (AesGcm.Proofs.byteArrayOfBits_size _).trans frontSizeEq
  have tailCipherSize : tailCipher.size = tailSize :=
    (AesGcm.Proofs.byteArrayOfBits_size _).trans tailSizeEq
  have splitCiphertext : frontCipher ++ tailCipher = ciphertext := by
    exact (CTR.gctr_bytes_append_blocks cipher initial front tail blocks frontSizeEq).symm.trans
      (congrArg (fun bytes : ByteArray ↦ AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR cipher initial (AesGcm.Spec.GCM.bitsOfByteArray bytes))) splitPlaintext)
  have frontStage : ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨next, []⟩ ∧
      next.label = (if tailSize = 0 then (if use256 then .l102b3e else .l1026de)
        else (if use256 then .l102abe else .l10265e)) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame counter.store next.store
        [span (fr.rsp - BitVec.ofNat 64 window) (window - 124), span destination frontSize] ∧
      ((next.arguments[5]'(by change 5 < 53; decide)).get 64).toNat = plaintext.size ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = destination ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 = source + BitVec.ofNat 64 frontSize ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = destination + BitVec.ofNat 64 frontSize ∧
      ((next.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = tailSize ∧
      Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock next.store (fr.rsp - 144)) = tailCounter ∧
      memLoad next.store (fr.rsp - 152) 64 = fr.rsi + 32 ∧
      (span destination frontSize).HasBytes next.store frontCipher := by
    by_cases small : plaintext.size < 17
    · have zeroFront : frontSize = 0 := by simp only [frontSize, blocks, small, ↓reduceIte, Nat.mul_zero]
      have sizeTail : tailSize = plaintext.size := by simp only [tailSize, zeroFront, Nat.sub_zero]
      have counterSmall : counter.label = (if use256 then .l102aaf else .l10264f) := by
        simpa only [maskLength, entryLength, lengthSize, small, ↓reduceIte] using counterLabel
      obtain ⟨next, run, label, store, n12, n14, keep, types⟩ :=
        Encrypt.small_runBlock use256 code counter.arguments counter.store
      have reach : (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨next, []⟩ := by
        have hloc : counter = ⟨(if use256 then .l102aaf else .l10264f), counter.arguments, counter.store⟩ := by
          cases counter with
          | mk entryLabelValue values mem =>
            change entryLabelValue = _ at counterSmall
            cases counterSmall
            rfl
        have hx : LIR.program.runBlock (dialect code) counter = .jump next := by
          rw [hloc]
          exact run
        exact .single (congrArg (Transfer.next (dialect code) []) hx)
      have nlabel : next.label = (if tailSize = 0 then (if use256 then .l102b3e else .l1026de)
          else (if use256 then .l102abe else .l10265e)) := by
        have hz : (counter.arguments[5]'(by change 5 < 53; decide)).get 64 = 0 ↔ plaintext.size = 0 := by
          constructor
          · intro hh
            rw [hh] at counterLengthNat
            simpa using counterLengthNat.symm
          · intro hh
            apply BitVec.eq_of_toNat_eq
            simpa [hh] using counterLengthNat
        simpa only [hz, sizeTail] using label
      refine ⟨next, reach, nlabel, ?_, types counterTyped, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [store]
        exact frameKeep _ _ _ counterFrameFull (shrinkKeep keep (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))
      · rw [store]
        exact .refl _ _
      · exact (congrArg BitVec.toNat (getKeep keep 5 (by decide))).trans counterLengthNat
      · exact (getKeep keep 13 (by decide)).trans counterDestination
      · simp only [zeroFront, BitVec.add_zero]
        exact (getKeep keep 15 (by decide)).trans counterSource
      · simpa [zeroFront] using n12.trans counterDestination
      · rw [n14, counterLengthNat, sizeTail]
      · rw [store, counterInitial]
        simp only [tailCounter, blocks, small, ↓reduceIte, Nat.repeat]
      · rw [store]
        exact counterKey
      · refine ⟨?_, ?_⟩
        · exact frontCipherSize
        · intro i
          have hi := i.isLt
          have hz : frontCipher.size = 0 := frontCipherSize.trans zeroFront
          have impossible : i.val < 0 := by simpa only [hz] using hi
          omega
    · have pos : 0 < plaintext.size := by omega
      have frontPositive : 0 < frontSize := by
        dsimp only [frontSize, blocks]
        simp only [small, ↓reduceIte]
        omega
      have sourceBound := hbuffer.2.2.2.2.1.low
      have destinationBound := (hwdst pos).readable.low
      have frontBytes : (span source front.size).HasBytes counter.store front := by
        have hh := hasBytes_extract counterBuffer.2.2.2.2.2.1 0 frontSize (by omega) frontLe
          (by have := source.isLt; omega)
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero, frontSizeEq] using hh
      have fullFrame : Atom.All code counter.arguments counter.store
          (if use256 then LIR.Fn102980.frameAt .l102a59 fr else LIR.Fn102520.frameAt .l1025f9 fr) := by
        cases use256 <;> exact counterFrame
      have fullLabel : counter.label = (if use256 then .l102a59 else .l1025f9) := by
        simpa only [maskLength, entryLength, lengthSize, small, ↓reduceIte] using counterLabel
      have stackSlice (base : BitVec 64) (hr : Readable fr.original base plaintext.size)
          (hs : (callStack fr).Disjoint (span base plaintext.size)) :
          (callStack fr).Disjoint (span base front.size) := by
        intro x hx hy
        apply hs x hx
        change base.toNat ≤ x ∧ x < base.toNat + front.size at hy
        change base.toNat ≤ x ∧ x < base.toNat + plaintext.size
        rw [frontSizeEq] at hy
        omega
      obtain ⟨full, fullRun, fullLabel, fullFrame, fullTyped, fullWrites,
        fullLength, fullDestination, fullSource, fullTailDestination, fullTailCount,
        fullCount, fullCounter, fullKey, fullBytes⟩ :=
        Encrypt.fullBlocks use256 code hcode key front length source destination fr counter
          fullLabel fullFrame counterTyped counterLengthEq counterSource counterDestination counterPtr
          (by rw [lengthSize]; exact lengthBound) (by rw [lengthSize]; omega)
          (by rw [frontSizeEq, lengthSize]; simp only [frontSize, blocks, small, ↓reduceIte])
          counterInput.1.1 scheduleRead counterKey
          (counterBuffer.2.2.2.2.1.of_offsets (addr_self _) (addr_self _) (by simp only [BitVec.sub_self, BitVec.toNat_zero]; rw [frontSizeEq]; omega))
          frontBytes
          (((hwdst pos).of_frame counterAllWrites).of_offsets (addr_self _) (addr_self _) (by simp only [BitVec.sub_self, BitVec.toNat_zero]; rw [frontSizeEq]; omega))
          (by rcases hbuffer.2.2.2.2.2.2 with heq | hdis
              · exact Or.inl heq
              · right; intro x hx hy
                apply hdis x
                · change source.toNat ≤ x ∧ x < source.toNat + plaintext.size
                  change source.toNat ≤ x ∧ x < source.toNat + front.size at hx
                  rw [frontSizeEq] at hx
                  omega
                · change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
                  change destination.toNat ≤ x ∧ x < destination.toNat + front.size at hy
                  rw [frontSizeEq] at hy
                  omega)
          (by intro r hr
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact scheduleSep
              · exact stackSlice source hbuffer.2.2.2.2.1 sourceSep
              · exact stackSlice destination (hwdst pos).readable destinationSep)
          (by intro x hx hy
              apply scheduleDataSep x ?_ hy
              change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
              change destination.toNat ≤ x ∧ x < destination.toNat + front.size at hx
              rw [frontSizeEq] at hx
              omega)
          (by intro a ha x hx hy
              apply hslots a ha x ?_ hy
              change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
              change destination.toNat ≤ x ∧ x < destination.toNat + front.size at hx
              rw [frontSizeEq] at hx
              omega)
      have fullCountNat : ((full.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = tailSize := by
        rw [fullTailCount, lengthSize, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : plaintext.size % 16 < 2^64)]
        dsimp only [tailSize, frontSize, blocks]
        simp only [small, ↓reduceIte]
        omega
      have fullZero : (full.arguments[14]'(by change 14 < 53; decide)).get 64 = 0 ↔ tailSize = 0 := by
        constructor
        · intro hh
          rw [hh] at fullCountNat
          simpa using fullCountNat.symm
        · intro hh
          apply BitVec.eq_of_toNat_eq
          simpa [hh] using fullCountNat
      obtain ⟨branched, branchRun, branchLabel, branchStore, branchSource, branchKeep, branchTypes⟩ :=
        Encrypt.afterFull_runBlock use256 code full.arguments full.store
      have branchReach : (LIR.program.sem (dialect code)).Reaches ⟨full, []⟩ ⟨branched, []⟩ := by
        have hloc : full = ⟨(if use256 then .l102aa2 else .l102642), full.arguments, full.store⟩ := by
          cases full with
          | mk fullLabelValue values mem =>
            change fullLabelValue = _ at fullLabel
            cases fullLabel
            rfl
        have hx : LIR.program.runBlock (dialect code) full = .jump branched := by
          rw [hloc]
          exact branchRun
        exact .single (congrArg (Transfer.next (dialect code) []) hx)
      have branchFrame : Atom.All code branched.arguments branched.store
          (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
        rw [branchStore]
        exact frameKeep _ _ _ fullFrame (shrinkKeep branchKeep (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))
      have bLength : ((branched.arguments[5]'(by change 5 < 53; decide)).get 64).toNat = plaintext.size := by
        exact (congrArg BitVec.toNat ((getKeep branchKeep 5 (by decide)).trans fullLength)).trans lengthSize
      have bDestination : (branched.arguments[13]'(by change 13 < 53; decide)).get 64 = destination := by
        exact (getKeep branchKeep 13 (by decide)).trans fullDestination
      have bSource : (branched.arguments[15]'(by change 15 < 53; decide)).get 64 = source + BitVec.ofNat 64 frontSize := by
        rw [branchSource, fullSource, frontSizeEq]
      have bTailDestination : (branched.arguments[12]'(by change 12 < 53; decide)).get 64 = destination + BitVec.ofNat 64 frontSize := by
        have hh := (getKeep branchKeep 12 (by decide)).trans fullTailDestination
        simp only [frontSizeEq] at hh
        exact hh
      have bCount : ((branched.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = tailSize := by
        exact (congrArg BitVec.toNat (getKeep branchKeep 14 (by decide))).trans fullCountNat
      have frameWrites : RamWriteFrame counter.store branched.store
          [span (fr.rsp - BitVec.ofNat 64 window) (window - 124), span destination frontSize] := by
        rw [branchStore]
        simpa only [frontSizeEq] using fullWrites
      have counterValue : Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock branched.store (fr.rsp - 144)) = tailCounter := by
        rw [branchStore, fullCounter, counterInitial, lengthSize]
        simp only [tailCounter, blocks, small, ↓reduceIte]
      have bKey : memLoad branched.store (fr.rsp - 152) 64 = fr.rsi + 32 := by
        rw [branchStore, fullKey]
      have bBytes : (span destination frontSize).HasBytes branched.store frontCipher := by
        rw [branchStore]
        simpa only [counterInitial, frontSizeEq] using fullBytes
      by_cases zero : tailSize = 0
      · have bLabel : branched.label = (if use256 then .l102aaa else .l10264a) := by
          simp only [fullZero, zero, ↓reduceIte] at branchLabel
          exact branchLabel
        obtain ⟨next, run, label, store, keep, types⟩ :=
          Encrypt.fullDone_runBlock use256 code branched.arguments branched.store
        have reach : (LIR.program.sem (dialect code)).Reaches ⟨branched, []⟩ ⟨next, []⟩ := by
          have hloc : branched = ⟨(if use256 then .l102aaa else .l10264a), branched.arguments, branched.store⟩ := by
            cases branched with
            | mk branchLabelValue values mem =>
              change branchLabelValue = _ at bLabel
              cases bLabel
              rfl
          have hx : LIR.program.runBlock (dialect code) branched = .jump next := by
            rw [hloc]
            exact run
          exact .single (congrArg (Transfer.next (dialect code) []) hx)
        refine ⟨next, fullRun.trans (branchReach.trans reach), ?_, ?_, types (branchTypes fullTyped), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [zero, ↓reduceIte]
          exact label
        · rw [store]
          exact frameKeep _ _ _ branchFrame (shrinkKeep keep (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))
        · rw [store]
          exact frameWrites
        · exact (congrArg BitVec.toNat (getKeep keep 5 (by decide))).trans bLength
        · exact (getKeep keep 13 (by decide)).trans bDestination
        · exact (getKeep keep 15 (by decide)).trans bSource
        · exact (getKeep keep 12 (by decide)).trans bTailDestination
        · exact (congrArg BitVec.toNat (getKeep keep 14 (by decide))).trans bCount
        · rw [store]
          exact counterValue
        · rw [store]
          exact bKey
        · rw [store]
          exact bBytes
      · refine ⟨branched, fullRun.trans branchReach, ?_, branchFrame, branchTypes fullTyped,
          frameWrites, bLength, bDestination, bSource, bTailDestination, bCount, counterValue, bKey, bBytes⟩
        simp only [fullZero, zero, ↓reduceIte] at branchLabel
        simp only [zero, ↓reduceIte]
        exact branchLabel
  have cipherStage : ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102b3e else .l1026de) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame counter.store next.store (Encrypt.ciphertextRegions use256 fr destination plaintext.size) ∧
      ((next.arguments[5]'(by change 5 < 53; decide)).get 64).toNat = plaintext.size ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = destination ∧
      (span destination plaintext.size).HasBytes next.store ciphertext := by
    obtain ⟨frontLoc, frontRun, frontLabel, frontFrame, frontTyped, frontWrites,
      frontLength, frontDestination, tailSource, tailDestination, tailCount,
      frontCounter, frontKey, frontBytes⟩ := frontStage
    have frontWritesLarge : RamWriteFrame counter.store frontLoc.store
        (Encrypt.ciphertextRegions use256 fr destination plaintext.size) := by
      apply (RamWriteFrame.refl _ _).trans frontWrites
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨span (fr.rsp - BitVec.ofNat 64 window) (window - 112), by simp [Encrypt.ciphertextRegions, window],
          Nat.le_refl _, ?_⟩
        simp only [span]
        omega
      · exact ⟨span destination plaintext.size, by simp [Encrypt.ciphertextRegions],
          Nat.le_refl _, by simp only [span]; omega⟩
    by_cases zero : tailSize = 0
    · have heq : frontCipher = ciphertext := by
        have empty : tailCipher = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (tailCipherSize.trans zero)
        simpa only [empty, ByteArray.append_empty] using splitCiphertext
      refine ⟨frontLoc, frontRun, ?_, frameAuth _ _ frontFrame, frontTyped, frontWritesLarge,
        frontLength, frontDestination, ?_⟩
      · simpa only [zero, ↓reduceIte] using frontLabel
      · have same : frontSize = plaintext.size := by dsimp only [tailSize] at zero; omega
        simpa only [same, heq] using frontBytes
    · have pos : 0 < plaintext.size := by dsimp only [tailSize] at zero; omega
      have sourceBound := hbuffer.2.2.2.2.1.low
      have destinationBound := (hwdst pos).readable.low
      have sourceOffset : (source + BitVec.ofNat 64 frontSize).toNat = source.toNat + frontSize := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have destinationOffset : (destination + BitVec.ofNat 64 frontSize).toNat = destination.toNat + frontSize := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have stackTail (base : BitVec 64) (ha : (base + BitVec.ofNat 64 frontSize).toNat = base.toNat + frontSize)
          (hs : (callStack fr).Disjoint (span base plaintext.size)) :
          (callStack fr).Disjoint (span (base + BitVec.ofNat 64 frontSize) tail.size) := by
        intro x hx hy
        apply hs x hx
        change (base + BitVec.ofNat 64 frontSize).toNat ≤ x ∧
          x < (base + BitVec.ofNat 64 frontSize).toNat + tail.size at hy
        rw [ha, tailSizeEq] at hy
        change base.toNat ≤ x ∧ x < base.toNat + plaintext.size
        dsimp only [tailSize] at hy
        omega
      have sourceTailSep := stackTail source sourceOffset sourceSep
      have destinationTailSep := stackTail destination destinationOffset destinationSep
      have tailBefore := hasBytes_extract counterBuffer.2.2.2.2.2.1 frontSize plaintext.size frontLe
        (Nat.le_refl _) (by omega)
      have tailBytes : (span (source + BitVec.ofNat 64 frontSize) tail.size).HasBytes frontLoc.store tail := by
        apply hasBytes_of_frame frontWrites
          (by simpa only [tailSizeEq] using tailBefore)
        · simp only [span, sourceOffset, tailSizeEq, tailSize]
          omega
        · intro r hr x hx hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · apply sourceTailSep x ?_ hx
            change (fr.rsp - BitVec.ofNat 64 window).toNat ≤ x ∧
              x < (fr.rsp - BitVec.ofNat 64 window).toNat + (window - 124) at hy
            rw [lower] at hy
            change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
            omega
          · rcases hbuffer.2.2.2.2.2.2 with heq | hdis
            · rw [heq] at hx
              simp only [MemoryRegion.Contains, span, destinationOffset, tailSizeEq, tailSize] at hx
              change destination.toNat ≤ x ∧ x < destination.toNat + frontSize at hy
              omega
            · apply hdis x ?_ ?_
              · change source.toNat ≤ x ∧ x < source.toNat + plaintext.size
                change (source + BitVec.ofNat 64 frontSize).toNat ≤ x ∧
                  x < (source + BitVec.ofNat 64 frontSize).toNat + tail.size at hx
                rw [sourceOffset, tailSizeEq] at hx
                dsimp only [tailSize] at hx
                omega
              · change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
                change destination.toNat ≤ x ∧ x < destination.toNat + frontSize at hy
                omega
      have frontAllWrites : RamWriteFrame fr.original frontLoc.store
          [fr.region, span destination plaintext.size] := by
        apply counterAllWritesFull.trans frontWrites
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [span, Activation.region, lower] <;> omega
        · exact ⟨span destination plaintext.size, by simp, Nat.le_refl _, by simp only [span]; omega⟩
      have frontInput := inputAfter frontAllWrites
      have labelTail : frontLoc.label = (if use256 then .l102abe else .l10265e) := by
        simpa only [zero, ↓reduceIte] using frontLabel
      obtain ⟨next, run, label, frame, types, keep, writes, bytes⟩ :=
        Encrypt.tailFromFrame use256 code hcode key tail
          (source + BitVec.ofNat 64 frontSize) (destination + BitVec.ofNat 64 frontSize)
          fr frontLoc.arguments frontLoc.store frontFrame frontTyped tailSource tailDestination
          (by rw [tailSizeEq]; exact tailCount) (by rw [tailSizeEq]; omega) (by rw [tailSizeEq]; exact tailLe)
          frontInput.1.1 (scheduleRead.of_frame frontWrites) frontKey
          ((hbuffer.2.2.2.2.1.of_frame frontAllWrites).sub (by rw [sourceOffset]; omega)
            (by rw [sourceOffset, tailSizeEq]; dsimp only [tailSize]; omega)) tailBytes
          (((hwdst pos).of_frame frontAllWrites).sub (by rw [destinationOffset]; omega)
            (by rw [destinationOffset, tailSizeEq]; dsimp only [tailSize]; omega))
          (by intro r hr
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact scheduleSep
              · exact sourceTailSep
              · exact destinationTailSep)
          (by intro a ha x hx hy
              apply hslots a (by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
                rcases ha with rfl | rfl <;> decide) x ?_ hy
              change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
              change (destination + BitVec.ofNat 64 frontSize).toNat ≤ x ∧
                x < (destination + BitVec.ofNat 64 frontSize).toNat + tail.size at hx
              rw [destinationOffset, tailSizeEq] at hx
              dsimp only [tailSize] at hx
              omega)
      have tailRun : (LIR.program.sem (dialect code)).Reaches ⟨frontLoc, []⟩ ⟨next, []⟩ := by
        have hloc : frontLoc = ⟨(if use256 then .l102abe else .l10265e), frontLoc.arguments, frontLoc.store⟩ := by
          cases frontLoc with
          | mk tailLabelValue values mem =>
            change tailLabelValue = _ at labelTail
            cases labelTail
            rfl
        rw [hloc]
        exact run
      have tailBytesOut : (span (destination + BitVec.ofNat 64 frontSize) tailSize).HasBytes next.store tailCipher := by
        simpa only [frontCounter, tailSizeEq] using bytes
      have frontBytesOut : (span destination frontSize).HasBytes next.store frontCipher := by
        apply hasBytes_of_frame writes frontBytes (by simp only [span]; omega)
        intro r hr x hx hy
        simp only [Encrypt.ciphertextRegions, show (if use256 then 0xb50 else 0x940) = window from rfl, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · apply destinationSep x ?_ ?_
          · change (fr.rsp - BitVec.ofNat 64 window).toNat ≤ x ∧
              x < (fr.rsp - BitVec.ofNat 64 window).toNat + (window - 112) at hy
            rw [lower] at hy
            change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
            omega
          · change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
            change destination.toNat ≤ x ∧ x < destination.toNat + frontSize at hx
            omega
        · apply destinationSep x ?_ ?_
          · change (fr.rsp - 64).toNat ≤ x ∧ x < (fr.rsp - 64).toNat + 16 at hy
            rw [sub64] at hy
            change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
            omega
          · change destination.toNat ≤ x ∧ x < destination.toNat + plaintext.size
            change destination.toNat ≤ x ∧ x < destination.toNat + frontSize at hx
            omega
        · simp only [MemoryRegion.Contains, span, destinationOffset, tailSizeEq] at hx hy
          omega
      have allWrites : RamWriteFrame counter.store next.store
          (Encrypt.ciphertextRegions use256 fr destination plaintext.size) := by
        apply frontWritesLarge.trans writes
        intro r hr
        simp only [Encrypt.ciphertextRegions, show (if use256 then 0xb50 else 0x940) = window from rfl, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨span (fr.rsp - BitVec.ofNat 64 window) (window - 112),
            by simp [Encrypt.ciphertextRegions, window], Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨span (fr.rsp - 64) 16, by simp [Encrypt.ciphertextRegions], Nat.le_refl _, Nat.le_refl _⟩
        · refine ⟨span destination plaintext.size, by simp [Encrypt.ciphertextRegions], ?_, ?_⟩ <;>
            simp only [span, destinationOffset, tailSizeEq, tailSize] <;> omega
      refine ⟨next, frontRun.trans tailRun, label, frame, types, allWrites, ?_, ?_, ?_⟩
      · exact (congrArg BitVec.toNat (getKeep keep 5 (by decide))).trans frontLength
      · exact (getKeep keep 13 (by decide)).trans frontDestination
      · have hbytes := hasBytes_append (front := frontCipher) (tail := tailCipher)
          (by simpa only [frontCipherSize] using frontBytesOut)
          (by simpa only [frontCipherSize, tailCipherSize] using tailBytesOut)
          (by rw [frontCipherSize]; omega : destination.toNat + frontCipher.size < 2^64)
        simpa only [frontCipherSize, tailCipherSize, splitCiphertext,
          show frontSize + tailSize = plaintext.size by dsimp only [tailSize]; omega] using hbytes
  obtain ⟨encrypted, cipherRun, cipherLabel, cipherFrame, cipherTyped, cipherWrites,
    cipherLength, cipherDestination, cipherBytes⟩ := cipherStage
  have cipherWritesFull : RamWriteFrame counter.store encrypted.store
      [fr.region, span destination plaintext.size] := by
    apply (RamWriteFrame.refl _ _).trans cipherWrites
    intro r hr
    simp only [Encrypt.ciphertextRegions, show (if use256 then 0xb50 else 0x940) = window from rfl, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [span, Activation.region, lower] <;> omega
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
        simp only [span, Activation.region, sub64] <;> omega
    · exact ⟨span destination plaintext.size, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have cipherAllWrites : RamWriteFrame fr.original encrypted.store [fr.region, span destination plaintext.size] :=
    counterAllWritesFull.trans cipherWritesFull (fun r hr ↦ ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have encryptedInput := inputAfter cipherAllWrites
  have encryptedMask : (span (fr.rsp - 80) 16).HasBytes encrypted.store ⟨maskValue.toArray⟩ := by
    apply hasBytes_of_frame cipherWrites counterMask
    · simp only [span, sub80]
      have := ef.slot.low
      omega
    · intro r hr x hx hy
      simp only [Encrypt.ciphertextRegions, show (if use256 then 0xb50 else 0x940) = window from rfl, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [MemoryRegion.Contains, span, sub80] at hx
        simp only [MemoryRegion.Contains, span, lower] at hy
        omega
      · simp only [MemoryRegion.Contains, span, sub80] at hx
        simp only [MemoryRegion.Contains, span, sub64] at hy
        omega
      · apply destinationSep x ?_ hy
        simp only [MemoryRegion.Contains, span, sub80] at hx
        change fr.low.toNat ≤ x ∧ x < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
        omega
  obtain ⟨output, authExec, ret, done, typed, authWrites, status, bytes, tagBytes⟩ :=
    Encrypt.authenticate use256 code hcode key nonce associatedData ciphertext maskValue
      destination fr encrypted cipherLabel cipherFrame cipherTyped encryptedInput
      (by intro pos; rw [cipherSize]; exact (hwdst (by omega)).readable.of_frame cipherAllWrites)
      (by simpa only [cipherSize] using cipherBytes) encryptedMask
      (by simpa only [cipherSize] using cipherLength) cipherDestination
      (by unfold AesGcm.Spec.GCM.maxAssociatedDataBytes; omega)
      (by rw [cipherSize]; unfold AesGcm.Spec.GCM.maxMessageBytes; omega)
      (hwresult.of_frame cipherAllWrites)
      (by intro r hr; apply hsep r
          simp only [cipherSize, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
      (by simpa only [cipherSize] using hresultsep _ (by simp))
  have throughCipher : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨(if use256 then .l102980 else .l102520), args, fr.original⟩, []⟩ ⟨encrypted, []⟩ :=
    entryRun.trans (maskRun.trans (counterRun.trans cipherRun))
  have exec : LIR.program.Exec (dialect code)
      ⟨⟨(if use256 then .l102980 else .l102520), args, fr.original⟩, []⟩ output :=
    Program.Exec.of_sem (throughCipher.exec authExec.sem)
  have allWrites : RamWriteFrame fr.original output.store
      [fr.region, span fr.rdi 17, span destination plaintext.size] := by
    have beforeAuth : RamWriteFrame fr.original encrypted.store
        [fr.region, span fr.rdi 17, span destination plaintext.size] := by
      apply (RamWriteFrame.refl _ _).trans cipherAllWrites
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨span destination plaintext.size, by simp, Nat.le_refl _, Nat.le_refl _⟩
    apply beforeAuth.trans authWrites
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨span fr.rdi 17, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have lengths : AesGcm.Spec.GCM.lengthsSupported associatedData.size plaintext.size = true := by
    change (decide (8 * plaintext.size ≤ 8 * (2^36 - 32)) &&
      decide (8 * associatedData.size ≤ 8 * (2^61 - 1))) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  have hkey : Standards.NIST.GCM.bitsOfBytes
      (Standards.NIST.AES.cipher (AES16.variant use256) key (Vector.replicate 16 0)) =
      cipher (Standards.NIST.GCM.zeros 128) := by
    have hz : Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.zeros 128) =
        Vector.replicate 16 (0 : UInt8) := by decide +kernel
    simp only [cipher, AesGcm.Spec.GCM.forwardCipher, hz]
  have hmaskValue : Standards.NIST.GCM.bitsOfBytes maskValue =
      cipher (Standards.NIST.GCM.preCounterBlock cipher (Standards.NIST.GCM.bitsOfBytes nonce)) := by
    rw [← Tag.bitsOfBytes_nonce96_counter_one]
    simp only [cipher, AesGcm.Spec.GCM.forwardCipher, AesGcm.Proofs.bytesOfBits_bitsOfBytes, maskValue]
  refine ⟨output, exec, ret, done, typed, allWrites, ciphertext, _, ?_, status, ?_, tagBytes⟩
  · exact Tag.ciphertextAndTag_eq_some (AES16.variant use256) key nonce associatedData
      plaintext ciphertext _ maskValue lengths rfl hkey hmaskValue
  · simpa only [cipherSize] using bytes

end AesGcm.Proofs.Machine.Core
