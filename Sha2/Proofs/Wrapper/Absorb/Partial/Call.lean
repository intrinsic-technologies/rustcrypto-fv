import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA256.Correctness
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Partial

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

set_option maxHeartbeats 800000 in
theorem compression_call [Bindings] {v : Variant}
    {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context (v := v) initial inputs)
    (input : Preserved (v := v) initial s)
    (words : HashStateAt s (stackPtr initial - 88) hash)
    (rip : s.RIP = (v.pc 0x13c))
    (rdi : s.regValue .rdi = stackPtr initial - 88)
    (rsi : s.regValue .rsi = stackPtr initial - 152) (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr initial - 152).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, Preserved (v := v) initial t ∧ t.RIP = (v.pc 0x141) ∧
      HashStateAt t (stackPtr initial - 88) (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk)) ∧
      memLoad t.external (stackPtr initial - 56) 64 = memLoad s.external (stackPtr initial - 56) 64 ∧
      PreservesABI s t := by
  obtain ⟨u, stateU, effect, rspU, returnU⟩ := Wrapper.call ctx input.toState
    (v.textOffset + 0x13c) (BitVec.ofNat 32 (0xb4e0 - (v.textOffset + 0x141))) (by cases v <;> decide) (by cases v <;> decide +kernel) (by cases v <;> decide)
    (by cases v <;> exact inProgram_of_textOffset 0xb4e0 (by decide)) rip input.rsp
  have entry : u.RIP = 0x10b4e0 := by cases v <;> exact effect.rip
  have callFrame := effect.agrees
  have slot : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rfl
  simp only [callEffect, pushEffect_components, slot] at callFrame
  have rdiU : u.regValue .rdi = stackPtr initial - 88 :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans rdi
  have rsiU : u.regValue .rsi = stackPtr initial - 152 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans rsi
  have rdxU : u.regValue .rdx = BitVec.ofNat 64 1 :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans count
  let layout : StackCallLayout 816 64 32 336 :=
    ⟨352, 152, 88, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by cases v <;> decide)⟩
  have pre := callee_pre_of_stack ctx.stride ctx.machine ctx.call stateU.machine
    stateU.directionFlag stateU.loaded stateU.allocated layout entry rspU rsiU rdiU
    (by
      rw [returnU]
      change InProgram (v.pc 0x13c + BitVec.ofNat 64 5)
      rw [Variant.pc_add]
      exact Variant.pc_inProgram v (by decide))
  have wordsU : HashStateAt u (u.regValue .rdi) hash := by
    rw [rdiU]
    apply Wrapper.hashState_of_bytes words
    intro i hi
    apply callFrame.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covers
    · obtain ⟨j, hj, eq⟩ := covers
      apply OffsetsApart.ne (c₁ := -352) (len₁ := 8) (c₂ := -88) (len₂ := 32)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by cases v <;> decide)
      simpa only [BitVec.sub_eq_add_neg] using eq.symm
    · exact covers
  have bounds := validCall_stack_bounds ctx.call
  have spNat : (stackPtr u).toNat = (stackPtr initial).toNat - 352 := by
    rw [rspU]
    exact validCall_stack_sub_toNat ctx.call (by cases v <;> decide)
  have compressionPre : CompressionPre u (returnBoundary initial) hash
      chunk 1 := {
    toCalleePre := pre
    countRegister := rdxU
    inputBytes := by
      change (⟨(u.regValue .rsi).toNat, 64⟩ : MemoryRegion).HasBytes u.external chunk
      rw [rsiU]
      refine ⟨bytes.1, fun i => ?_⟩
      have byte := bytes.2 i
      change u.external[BitVec.ofNat 64 ((stackPtr initial - 152).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [callFrame.byte (x := stackPtr initial - 152 + BitVec.ofNat 64 i.val) ?_]
      · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
      · intro c hc covers
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact covers
        · obtain ⟨j, hj, eq⟩ := covers
          apply OffsetsApart.ne (c₁ := -352) (len₁ := 8) (c₂ := -152) (len₂ := 64)
            (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj
            (show i.val < 64 from by have hsize : chunk.size = 64 := bytes.1; omega) (by cases v <;> decide)
          simpa only [BitVec.sub_eq_add_neg] using eq.symm
        · exact covers
    hashWords := wordsU
  }
  obtain ⟨t, result⟩ := compression_correct compressionPre (by
    rw [returnU]
    change InProgram (v.pc 0x13c + BitVec.ofNat 64 5)
    rw [Variant.pc_add]
    exact Variant.pc_inProgram v (by decide))
  have stateT := stateU.of_callee (outputOffset := 88) ctx result.toCalleeResult rspU rdiU
    (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
  have rspT : stackPtr t = stackPtr initial - 344 := by
    change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr u + 8 = _
    rw [rspU]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have abiCall : PreservesABI s u := by
    apply preservesABI_of_agrees callFrame input.directionFlag
    intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact callFrame.read (n := 64) (r := 3) (by simp)
    · exact callFrame.read (n := 64) (r := 5) (by simp)
    · exact callFrame.read (n := 64) (r := 12) (by simp)
    · exact callFrame.read (n := 64) (r := 13) (by simp)
    · exact callFrame.read (n := 64) (r := 14) (by simp)
    · exact callFrame.read (n := 64) (r := 15) (by simp)
    all_goals simp
  have abi : PreservesABI s t :=
    ⟨fun reg member => (result.abi.1 reg member).trans (abiCall.1 reg member),
      result.abi.2.1, result.abi.2.2.1.trans abiCall.2.2.1,
      result.abi.2.2.2.trans abiCall.2.2.2⟩
  have stackRegion : Stack.region u 336 =
      (⟨(stackPtr initial - 688).toNat, 344⟩ : MemoryRegion) := by
    have base : (stackPtr initial-688).toNat = (stackPtr initial).toNat-688 :=
      validCall_stack_sub_toNat ctx.call (offset := 688) (by cases v <;> decide)
    change (⟨(stackPtr u).toNat-336, (stackPtr u).toNat+8-((stackPtr u).toNat-336)⟩ : MemoryRegion) = _
    rw [spNat]
    change (⟨(stackPtr initial).toNat-352-336,
      (stackPtr initial).toNat-352+8-((stackPtr initial).toNat-352-336)⟩ : MemoryRegion) = _
    have startEq : (stackPtr initial).toNat-352-336 = (stackPtr initial-688).toNat := by
      rw [base]
      omega
    have sizeEq : (stackPtr initial).toNat-352+8-((stackPtr initial).toNat-352-336) = 344 := by omega
    rw [sizeEq, startEq]
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - 88).toNat, 32⟩ : MemoryRegion),
      (⟨(stackPtr initial - 688).toNat, 344⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        refine ⟨⟨(stackPtr initial-688).toNat,344⟩, by simp, ?_⟩
        have low : (stackPtr initial-688).toNat = (stackPtr initial).toNat-688 :=
          validCall_stack_sub_toNat ctx.call (offset := 688) (by cases v <;> decide)
        have slotNat : (stackPtr initial-352).toNat = (stackPtr initial).toNat-352 :=
          validCall_stack_sub_toNat ctx.call (by cases v <;> decide)
        change (stackPtr initial-688).toNat ≤ _ ∧ _ < (stackPtr initial-688).toNat+344
        rw [low, BitVec.toNat_add, slotNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        constructor <;> omega
      · exact covers.elim
    · simpa only [stackRegion, registerRegion, rdiU] using result.frame
  have preserved := Wrapper.preserved_of_bytes input stateT rspT (by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact Wrapper.frame_bytes ctx frame (offset := 176) (len := 24)
      (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide) (by cases v <;> decide) (.inl (by cases v <;> decide)) i hi)
  refine ⟨t, preserved, (result.rip.trans returnU).trans (by change v.pc _ + BitVec.ofNat 64 5 = v.pc _; rw [Variant.pc_add]), ?_, ?_, abi⟩
  · simpa only [rdiU, compressBlocks_single hash chunk bytes.1] using result.hashWords
  · apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (Wrapper.frame_bytes ctx frame (offset := 56) (len := 8)
      (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide) (by cases v <;> decide) (.inr (by cases v <;> decide)) i hi)

end Sha2.Proofs.Wrapper.Absorb.Partial
