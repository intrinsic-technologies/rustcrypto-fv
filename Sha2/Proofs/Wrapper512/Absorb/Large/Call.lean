import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Call
import Sha2.Proofs.Common.SHA512.Correctness
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

def fillDisplacement (v : Variant) (form : Form) : BitVec 32 :=
  BitVec.ofNat 32 (0x10dd00 - (0x100000 + v.textOffset form + (v.traversal form).fillCall + 5))

theorem fill_call_facts (v : Variant) (form : Form) (nonDigest : form ≠ .digest) :
    v.textOffset form + (v.traversal form).fillCall + 5 ≤ 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset form + (v.traversal form).fillCall) 5 =
      encodeCallRel32 (fillDisplacement v form) ∧
    branchTarget (v.pc (v.traversal form).fillCall form) 5
      (BitVec.signExtend 64 (fillDisplacement v form)) = 0x10dd00 ∧
    v.textOffset form + ((v.traversal form).fillCall + 5) < 71757 := by
  cases form <;> cases v <;> first | exact False.elim (nonDigest rfl) | decide +revert +kernel

set_option maxHeartbeats 800000 in
theorem compression_call [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form)
    (input : Preserved v initial s form)
    (words : HashStateAt s (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash) hash)
    (rip : s.RIP = v.pc (v.traversal form).fillCall form)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash)
    (rsi : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer) (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat, 128⟩ : MemoryRegion).HasBytes s.external chunk)
    (nonDigest : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc ((v.traversal form).fillCall + 5) form ∧
      HashStateAt t (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash) (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk)) ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 = memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 = memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 ∧
      PreservesABI s t ∧ MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat, 64⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, 424⟩ : MemoryRegion)] ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have facts := fill_call_facts v form nonDigest
  obtain ⟨u0, stateU0, effect, rspU0, returnU0, runU0⟩ := call_local ctx input.toState
    (v.textOffset form + (v.traversal form).fillCall) (fillDisplacement v form) facts.1
    facts.2.1 (by rw [show Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + (v.traversal form).fillCall) = v.pc (v.traversal form).fillCall form from rfl, facts.2.2.1]; decide)
    (by rw [show Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + (v.traversal form).fillCall) = v.pc (v.traversal form).fillCall form from rfl, facts.2.2.1]; exact inProgram_of_textOffset 0xdd00 (by decide)) rip input.rsp
  have entry0 : u0.RIP = 0x10dd00 := effect.rip.trans facts.2.2.1
  obtain ⟨u, stateU, entry, thunkRun, thunkFrame⟩ := compress512_thunk ctx stateU0 entry0
  have slot : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rw [BitVec.ofNat_add]
    rfl
  have callFrame0 := effect.agrees
  simp only [callEffect, pushEffect_components, slot] at callFrame0
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s u :=
    (callFrame0.trans thunkFrame).mono (by simp)
  have rspU : stackPtr u = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) :=
    (thunkFrame.read (n := 64) (r := 4) (by simp)).trans rspU0
  have returnU : (returnBoundary u).rip = v.pc ((v.traversal form).fillCall + 5) form := by
    change memLoad u.external (stackPtr u) 64 = _
    rw [show stackPtr u = stackPtr u0 from thunkFrame.read (n := 64) (r := 4) (by simp),
      thunkFrame.external (by simp [Component.Covers])]
    exact returnU0.trans (Variant.pc_add v (v.traversal form).fillCall 5 form)
  have rdiU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans rdi
  have rsiU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans rsi
  have rdxU : u.regValue .rdx = BitVec.ofNat 64 1 :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans count
  let layout : Wrapper.StackCallLayout form.stackBytes 128 64 416 :=
    ⟨form.frameBytes+8, form.activeMemory.buffer, form.activeMemory.hash, by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide, by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide, by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide, by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide,
      by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide, by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> decide, .inl (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))⟩
  have pre := callee_pre_of_stack ctx stateU layout entry rspU rsiU rdiU
    (by
      rw [returnU]
      exact inProgram_of_textOffset (v.textOffset form + ((v.traversal form).fillCall + 5)) facts.2.2.2)
  have wordsU : HashStateAt u (u.regValue .rdi) hash := by
    rw [rdiU]
    apply hashState_of_bytes words
    intro i hi
    apply callFrame.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covers
    · obtain ⟨j, hj, eq⟩ := covers
      apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.frameBytes + 8)) (len₁ := 8) (c₂ := -BitVec.ofNat 64 form.activeMemory.hash) (len₂ := 64)
        (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> unfold OffsetsApart <;> decide +kernel) (stackPtr initial) hj hi (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
      simpa only [BitVec.sub_eq_add_neg] using eq.symm
    · exact covers
  have budget := show form.stackBytes = form.frameBytes + 552 from by cases form <;> rfl
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have spNat : (stackPtr u).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) := by
    rw [rspU]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  have compressionPre : CompressionPre u (returnBoundary initial) hash
      chunk 1 := {
    toCalleePre := pre
    countRegister := rdxU
    inputBytes := by
      change (⟨(u.regValue .rsi).toNat, 128⟩ : MemoryRegion).HasBytes u.external chunk
      rw [rsiU]
      refine ⟨bytes.1, fun i => ?_⟩
      have byte := bytes.2 i
      change u.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [callFrame.byte (x := stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer + BitVec.ofNat 64 i.val) ?_]
      · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
      · intro c hc covers
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact covers
        · obtain ⟨j, hj, eq⟩ := covers
          apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.frameBytes + 8)) (len₁ := 8) (c₂ := -BitVec.ofNat 64 form.activeMemory.buffer) (len₂ := 128)
            (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> unfold OffsetsApart <;> decide +kernel) (stackPtr initial) hj
            (show i.val < 128 from by have hsize : chunk.size = 128 := bytes.1; omega) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
          simpa only [BitVec.sub_eq_add_neg] using eq.symm
        · exact covers
    hashWords := wordsU
  }
  obtain ⟨t, result⟩ := compression_correct_of_block body compressionPre (by
    rw [returnU]
    exact inProgram_of_textOffset (v.textOffset form + ((v.traversal form).fillCall + 5)) facts.2.2.2)
  have stateT := stateU.of_callee (outputOffset := form.activeMemory.hash) ctx result.toCalleeResult rspU rdiU
    (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
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
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, 424⟩ : MemoryRegion) := by
    have base : (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat = (stackPtr initial).toNat-(form.frameBytes + 424) :=
      Dispatch.stack_sub_toNat512 ctx (offset := (form.frameBytes + 424)) (by change _ ≤ form.stackBytes; omega)
    change (⟨(stackPtr u).toNat-416, (stackPtr u).toNat+8-((stackPtr u).toNat-416)⟩ : MemoryRegion) = _
    rw [spNat]
    change (⟨(stackPtr initial).toNat-(form.frameBytes + 8)-416,
      (stackPtr initial).toNat-(form.frameBytes + 8)+8-((stackPtr initial).toNat-(form.frameBytes + 8)-416)⟩ : MemoryRegion) = _
    have startEq : (stackPtr initial).toNat-(form.frameBytes + 8)-416 = (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat := by
      rw [base]
      omega
    have sizeEq : (stackPtr initial).toNat-(form.frameBytes + 8)+8-((stackPtr initial).toNat-(form.frameBytes + 8)-416) = 424 := by omega
    rw [sizeEq, startEq]
  have frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat, 64⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, 424⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        refine ⟨⟨(stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat,424⟩, by simp, ?_⟩
        have low : (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat = (stackPtr initial).toNat-(form.frameBytes + 424) :=
          Dispatch.stack_sub_toNat512 ctx (offset := (form.frameBytes + 424)) (by change _ ≤ form.stackBytes; omega)
        have slotNat : (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 8)).toNat = (stackPtr initial).toNat-(form.frameBytes + 8) :=
          Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
        change (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat ≤ _ ∧ _ < (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat+424
        rw [low, BitVec.toNat_add, slotNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        constructor <;> omega
      · exact covers.elim
    · simpa only [stackRegion, registerRegion, rdiU] using result.frame
  have frameGeneric : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat, 64⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, (form.frameBytes + 424)-form.frameBytes⟩ : MemoryRegion)] := by
    simpa only [Nat.add_sub_cancel_left] using frame
  have preserved := preserved_of_bytes input stateT (by
    cases form with
    | digest => trivial
    | slices =>
      intro a ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact frame_bytes ctx frameGeneric (offset := 624) (len := 24)
        (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
        (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (.inl (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))) i hi
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      intro offset member a ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        exact frame_bytes ctx frameGeneric (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
          (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) i hi)
    (fun _ => abi.1 .rbx (by simp))
    (fun _ => .inl (abi.1 _ (by cases v <;> simp)))
  obtain ⟨fuel, run⟩ := result.execution
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] :=
    memoryWriteFrame_trans (callFrame.memoryWriteFrame (call_stack_writes ctx))
      (callee_stack_frame ctx result.toCalleeResult rspU rdiU
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel)
        (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide +kernel) (by decide))
  refine ⟨t, preserved, result.rip.trans returnU, ?_, ?_, ?_, abi, frame,
    ⟨_, (runU0.trans thunkRun).trans run⟩, stackFrame⟩
  · simpa only [rdiU, compressBlocks_single hash chunk bytes.1] using result.hashWords
  · apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (frame_bytes ctx frameGeneric (offset := form.activeMemory.countLow) (len := 8)
      (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
      (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (.inr (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))) i hi)
  · apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (frame_bytes ctx frameGeneric (offset := form.activeMemory.countHigh) (len := 8)
      (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))
      (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide)) (.inr (by cases form <;> (try dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory]) <;> first | decide | (split <;> decide))) i hi)

end Sha2.Proofs.Wrapper512.Absorb.Large
