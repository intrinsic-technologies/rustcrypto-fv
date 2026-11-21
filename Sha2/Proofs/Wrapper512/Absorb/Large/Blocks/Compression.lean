import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Common.SHA512.Correctness
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

theorem source_bytes [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    (ctx : Context v initial inputs form) (state : ReturnState v initial s form)
    (i : Fin inputs.size) {offset count : Nat} (bound : offset + count ≤ inputs[i].bytes.size) :
    (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ : MemoryRegion).HasBytes
      s.external (inputs[i].bytes.extract offset (offset + count)) := by
  have size : (inputs[i].bytes.extract offset (offset+count)).size = count := by
    rw [ByteArray.size_extract, Nat.min_eq_left bound]
    omega
  refine ⟨size, ?_⟩
  intro j
  have hj : j.val < count := by simpa only [size] using j.isLt
  have byte := Copy.input_byte_unchanged ctx state.frame i ⟨offset+j.val, by omega⟩
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_assoc, ByteArray.getElem_extract] using byte

def compressionOffset (form : Form := .slices) (v : Variant := .sha384) : Nat :=
  match form with
  | .slices => 0x1c5
  | .digest => 0x122
  | _ => (v.traversal form).blocksCall

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem compress_slice [Bindings] (body : Compression.BlockCorrect) {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    {hash : Array UInt64} {offset count : Nat}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form) (i : Fin inputs.size)
    (bound : offset + 128*count ≤ inputs[i].bytes.size)
    (rip : s.RIP = v.pc (compressionOffset form v) form)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash)
    (rsi : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset)
    (rdx : s.regValue .rdx = BitVec.ofNat 64 count)
    (hashWords : HashStateAt s (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash) hash) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (compressionOffset form v + 5) form ∧
      HashStateAt t (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash)
        (compressBlocks hash (inputs[i].bytes.extract offset (offset + 128*count))) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat, 64⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat, 424⟩ : MemoryRegion)] ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have frameLow : 424 ≤ form.frameBytes := by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  let displacement : BitVec 32 := BitVec.ofNat 32 (0x10dd00 - (0x100000 + v.textOffset form + compressionOffset form v + 5))
  have targetEq : branchTarget (v.pc (compressionOffset form v) form) 5
      (displacement.signExtend 64) = 0x10dd00 := by
    cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  obtain ⟨u0, stateU0, effect, rspU0, returnU0, runCall⟩ := call_local ctx input.toState
    (v.textOffset form + compressionOffset form v) displacement (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
    (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
    (by rw [show (Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + compressionOffset form v)) = v.pc (compressionOffset form v) form from rfl, targetEq]; exact inProgram_of_textOffset 0xdd00 (by decide)) rip input.rsp
  have entry0 : u0.RIP = 0x10dd00 := effect.rip.trans (by change branchTarget _ _ _ = _; cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
  obtain ⟨u, stateU, entry, runThunk, thunkFrame⟩ := compress512_thunk ctx stateU0 entry0
  have slot : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, input.rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have callFrame0 := effect.agrees
  simp only [callEffect, pushEffect_components, slot] at callFrame0
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u :=
    (callFrame0.trans thunkFrame).mono (by simp)
  have rspU : stackPtr u = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) :=
    (thunkFrame.read (n := 64) (r := 4) (by simp)).trans rspU0
  have returnU : (returnBoundary u).rip = v.pc (compressionOffset form v + 5) form := by
    change memLoad u.external (stackPtr u) 64 = _
    rw [show stackPtr u = stackPtr u0 from thunkFrame.read (n := 64) (r := 4) (by simp),
      thunkFrame.external (by simp [Component.Covers])]
    exact returnU0.trans (Variant.pc_add v (compressionOffset form v) 5 form)
  have rdiU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans rdi
  have rsiU : u.regValue .rsi = inputs[i].address + BitVec.ofNat 64 offset :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans rsi
  have rdxU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans rdx
  have slices := Copy.source_region ctx stateU i bound
  have region : registerRegion u .rsi (128*count) =
      (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, 128*count⟩ : MemoryRegion) := by
    simp only [registerRegion, rsiU]
  have pre := callee_pre (inputBytes := 128*count) (outputBytes := 64)
    (outputOffset := form.activeMemory.hash) (reserve := 416) ctx stateU entry rspU rdiU
    (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by decide) (region ▸ slices.1) (region ▸ slices.2.1)
    (region ▸ slices.2.2) (by rw [returnU]; apply inProgram_of_textOffset; cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
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
      apply OffsetsApart.ne (c₁ := -(BitVec.ofNat 64 (form.frameBytes + 8))) (len₁ := 8) (c₂ := -(BitVec.ofNat 64 form.activeMemory.hash)) (len₂ := 64)
        (by cases form <;> unfold OffsetsApart <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using eq.symm
    · exact covers
  have budget : form.frameBytes + 8 + 416 ≤ form.stackBytes := by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have spNat : (stackPtr u).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) := by
    rw [rspU]
    exact Dispatch.stack_sub_toNat512 ctx (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
  have compressionPre : CompressionPre u (returnBoundary initial) hash
      (inputs[i].bytes.extract offset (offset + 128*count)) count := {
    toCalleePre := pre
    countRegister := rdxU
    inputBytes := by
      rw [region]
      exact source_bytes ctx stateU i bound
    hashWords := wordsU
  }
  obtain ⟨t, result⟩ := compression_correct_of_block body compressionPre (by
    rw [returnU]
    apply inProgram_of_textOffset; cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
  have stateT := stateU.of_callee (outputOffset := form.activeMemory.hash) ctx result.toCalleeResult rspU rdiU
    (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by decide)
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
  have stackRegion : Stack.region u 416 =
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat, 424⟩ : MemoryRegion) := by
    have base : (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat = (stackPtr initial).toNat - (form.frameBytes + 8 + 416) :=
      Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 8 + 416) (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
    change (⟨(stackPtr u).toNat-416, (stackPtr u).toNat+8-((stackPtr u).toNat-416)⟩ : MemoryRegion) = _
    rw [spNat]
    change (⟨(stackPtr initial).toNat - (form.frameBytes + 8)-416,
      (stackPtr initial).toNat - (form.frameBytes + 8)+8-((stackPtr initial).toNat - (form.frameBytes + 8)-416)⟩ : MemoryRegion) = _
    have startEq : (stackPtr initial).toNat - (form.frameBytes + 8)-416 = (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat := by
      rw [base]
      omega
    have sizeEq : (stackPtr initial).toNat - (form.frameBytes + 8)+8-((stackPtr initial).toNat - (form.frameBytes + 8)-416) = 424 := by omega
    rw [sizeEq, startEq]
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat, 64⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat, 424⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        refine ⟨⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat,424⟩, by simp, ?_⟩
        have low : (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat = (stackPtr initial).toNat - (form.frameBytes + 8 + 416) :=
          Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 8 + 416) (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
        have slotNat : (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) :=
          Dispatch.stack_sub_toNat512 ctx (by cases v <;> cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
        change (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat ≤ _ ∧ _ < (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8 + 416)).toNat+424
        rw [low, BitVec.toNat_add, slotNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        constructor <;> omega
      · exact covers.elim
    · simpa only [stackRegion, registerRegion, rdiU] using result.frame
  refine ⟨t, preserved_of_bytes input stateT ?_ (fun _ => abi.1 .rbx (by simp))
      (fun _ => .inl (abi.1 _ (by cases v <;> simp))),
    result.rip.trans returnU, ?_, abi, frame, ?_, ?_⟩
  · cases form
    case digest => trivial
    case slices =>
      intro a ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact frame_bytes ctx frame (by decide) (by decide) (by decide) (by decide)
        (by decide : 624 ≤ 632) (by decide : 24 ≤ 624) (.inl (by decide)) j hj
    case' reset stage =>
      have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases h with rfl | rfl | rfl
    case' finalizeIntoReset second => cases second
    case' traitFinalizeIntoReset second => cases second
    all_goals
      intro slot member a ha
      obtain ⟨j,hj,rfl⟩ := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals
        exact frame_bytes ctx frame (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) j hj
  · simpa only [rdiU] using result.hashWords
  · obtain ⟨fuel, run⟩ := result.execution
    exact ⟨_, (runCall.trans runThunk).trans run⟩
  · exact memoryWriteFrame_trans (call_stack_frame ctx effect input.rsp)
      (memoryWriteFrame_trans
        (thunkFrame.memoryWriteFrame (by simp [WritesWithin, Component.Covers]))
        (callee_stack_frame ctx result.toCalleeResult rspU rdiU
          (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))
          (by cases form <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by decide)))

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
