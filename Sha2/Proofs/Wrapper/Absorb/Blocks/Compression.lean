import Sha2.Proofs.Wrapper.Absorb.Copy
import Sha2.Proofs.Common.SHA256.Correctness
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem source_bytes [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    (ctx : Context (v := v) initial inputs) (state : State (v := v) initial s)
    (i : Fin inputs.size) {offset count : Nat} (bound : offset + count ≤ inputs[i].bytes.size) :
    (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ : MemoryRegion).HasBytes
      s.external (inputs[i].bytes.extract offset (offset + count)) := by
  have size : (inputs[i].bytes.extract offset (offset+count)).size = count := by
    rw [ByteArray.size_extract, Nat.min_eq_left bound]
    omega
  refine ⟨size, ?_⟩
  intro j
  have hj : j.val < count := by simpa only [size] using j.isLt
  have byte := validCall_input_byte_unchanged ctx.call state.frame i ⟨offset+j.val, by omega⟩
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_assoc, ByteArray.getElem_extract] using byte

theorem compress_slice [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {hash : Array UInt32} {offset count : Nat}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s) (i : Fin inputs.size)
    (bound : offset + 64*count ≤ inputs[i].bytes.size)
    (rip : s.RIP = (v.pc 0x168))
    (rdi : s.regValue .rdi = stackPtr initial - 88)
    (rsi : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (rdx : s.regValue .rdx = BitVec.ofNat 64 count)
    (hashWords : HashStateAt s (stackPtr initial - 88) hash) :
    ∃ t, Preserved (v := v) initial t ∧ t.RIP = (v.pc 0x16d) ∧
      HashStateAt t (stackPtr initial - 88)
        (compressBlocks hash (inputs[i].bytes.extract offset (offset + 64*count))) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - 88).toNat, 32⟩ : MemoryRegion),
        (⟨(stackPtr initial - 688).toNat, 344⟩ : MemoryRegion)] := by
  obtain ⟨u, stateU, effect, rspU, returnU⟩ := Wrapper.call ctx input.toState
    (v.textOffset + 0x168) (BitVec.ofNat 32 (0xb4e0 - (v.textOffset + 0x16d))) (by cases v <;> decide) (by cases v <;> decide +kernel) (by cases v <;> decide)
    (by cases v <;> exact inProgram_of_textOffset 0xb4e0 (by decide)) rip input.rsp
  have callFrame := effect.agrees
  have slot : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rfl
  simp only [callEffect, pushEffect_components, slot] at callFrame
  have rdiU : u.regValue .rdi = stackPtr initial - 88 :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans rdi
  have rsiU : u.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans rsi
  have rdxU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans rdx
  have slices := Copy.source_region ctx stateU i bound
  have region : registerRegion u .rsi (64*count) =
      (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, 64*count⟩ : MemoryRegion) := by
    simp only [registerRegion, rsiU]
  have pre := callee_pre (inputBytes := 64*count) (outputBytes := 32)
    (outputOffset := 88) (reserve := 336) ctx stateU (show u.RIP = 0x10b4e0 by cases v <;> exact effect.rip) rspU rdiU
    (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide) (region ▸ slices.1) (region ▸ slices.2.1)
    (region ▸ slices.2.2) (by
      rw [returnU]
      change InProgram (v.pc 0x168 + BitVec.ofNat 64 5)
      rw [Variant.pc_add]
      exact Variant.pc_inProgram v (by decide))
  have wordsU : HashStateAt u (u.regValue .rdi) hash := by
    rw [rdiU]
    apply hashState_of_bytes hashWords
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
      (inputs[i].bytes.extract offset (offset + 64*count)) count := {
    toCalleePre := pre
    countRegister := rdxU
    inputBytes := by
      rw [region]
      exact source_bytes ctx stateU i bound
    hashWords := wordsU
  }
  obtain ⟨t, result⟩ := compression_correct compressionPre (by
    rw [returnU]
    change InProgram (v.pc 0x168 + BitVec.ofNat 64 5)
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
  refine ⟨t, preserved_of_bytes input stateT rspT ?_,
    (result.rip.trans returnU).trans (by change v.pc _ + BitVec.ofNat 64 5 = v.pc _; rw [Variant.pc_add]), ?_, abi, frame⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact frame_bytes ctx frame (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
      (by cases v <;> decide : 176 ≤ 344) (by cases v <;> decide : 24 ≤ 176) (.inl (by cases v <;> decide)) j hj
  · simpa only [rdiU] using result.hashWords

end Sha2.Proofs.Wrapper.Absorb.Blocks
