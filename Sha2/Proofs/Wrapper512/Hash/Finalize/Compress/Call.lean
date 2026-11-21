import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Wrapper512.Call
import Sha2.Proofs.Wrapper512.Hash.Finalize.Compress.Machine
import Sha2.Proofs.Common.SHA512.Correctness
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Compress

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper512.Absorb

def copyOutputOffset : Form → Nat
  | .slices | .digest | .reset _ | .traitFinalizeIntoReset true => 176
  | .finalizeIntoReset false => 392
  | .finalizeIntoReset true => 176
  | .traitFinalizeIntoReset false => 616

theorem hashPointerState_of_abi {v : Variant} {form : Form} {initial s t : RamState}
    (pointer : hashPointerState v form initial s) (abi : PreservesABI s t) :
    hashPointerState v form initial t := by
  cases form with
  | slices | digest => exact (abi.1 .r14 (by simp)).trans pointer
  | reset stage => trivial
  | finalizeIntoReset second =>
    cases second with
    | false => trivial
    | true => exact (abi.1 .rbx (by simp)).trans pointer
  | traitFinalizeIntoReset second =>
    cases second with
    | true => exact (abi.1 .rbx (by simp)).trans pointer
    | false =>
      cases v <;> exact ⟨(abi.1 _ (by simp)).trans pointer.1,
        (abi.1 _ (by simp)).trans pointer.2⟩

theorem preserved_slot_bounds (form : Form) (reset : form.twoOutputs = true) :
    ∀ offset ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot],
      offset ≤ form.frameBytes ∧ 8 ≤ offset ∧
      (form.finalMemory.hash + 8 ≤ offset ∨ offset + 64 ≤ form.finalMemory.hash) := by
  cases form <;> first | contradiction | decide +revert +kernel

def layout (form : Form) : Wrapper.StackCallLayout form.stackBytes 128 64 416 :=
  ⟨form.frameBytes + 8, copyOutputOffset form, form.finalMemory.hash,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel,
    by cases form <;> decide +revert +kernel⟩

theorem frame_bounds (form : Form) :
    form.frameBytes + 8 ≤ form.stackBytes ∧
    form.frameBytes + 424 ≤ form.stackBytes ∧
    form.stackBytes = form.frameBytes + 552 ∧
    112 ≤ form.finalMemory.hash ∧ form.finalMemory.hash ≤ form.frameBytes := by
  cases form <;> decide +revert +kernel

theorem call_hash_apart (form : Form) :
    OffsetsApart (-BitVec.ofNat 64 (form.frameBytes + 8)) 8
      (-BitVec.ofNat 64 form.finalMemory.hash) 64 := by
  cases form <;> unfold OffsetsApart <;> decide +revert +kernel

theorem call_input_apart (form : Form) :
    OffsetsApart (-BitVec.ofNat 64 (form.frameBytes + 8)) 8
      (-BitVec.ofNat 64 (copyOutputOffset form)) 128 := by
  cases form <;> unfold OffsetsApart <;> decide +revert +kernel

def displacement (v : Variant) (form : Form) (last : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (0x10dd00 - (0x100000 + v.textOffset form + callOffset v form last + 5))

theorem call_site (v : Variant) (form : Form) (last : Bool) :
    v.textOffset form + callOffset v form last + 5 ≤ 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset form + callOffset v form last) 5 =
      encodeCallRel32 (displacement v form last) ∧
    branchTarget (Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + callOffset v form last))
      5 ((displacement v form last).signExtend 64) = 0x10dd00 ∧
    v.textOffset form + (callOffset v form last + 5) < 71757 := by
  cases form <;> cases v <;> cases last <;> decide +revert +kernel


set_option maxHeartbeats 800000 in
theorem call [Bindings] (body : Compression.BlockCorrect) (last : Bool)
    {form : Form} {v : Variant} {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt64}
    (ctx : Context v initial inputs form)
    (input : HashAt v initial s hash form)
    (rip : s.RIP = v.pc (callOffset v form last) form)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash)
    (rsi : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)) (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat, 128⟩ : MemoryRegion).HasBytes s.external chunk)
    :
    ∃ fuel t, HashAt v initial t (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk)) form ∧
      t.RIP = s.RIP + 5 ∧ PreservesABI s t ∧
      Advances (returnBoundary initial) fuel s t ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash).toNat, 64⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, 424⟩ : MemoryRegion)] := by
  let pc : Nat := callOffset v form last
  let disp := displacement v form last
  have site := call_site v form last
  have fb := frame_bounds form
  have targetEq : branchTarget (Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + pc))
      5 (disp.signExtend 64) = 0x10dd00 := site.2.2.1
  obtain ⟨u0, stateU0, effect, rspU0, returnU0, runU0⟩ := Wrapper512.call_local ctx input.toState
    ((v.textOffset form) + pc) disp site.1 site.2.1
    (by rw [targetEq]; decide +kernel)
    (by rw [targetEq]; exact inProgram_of_textOffset 0xdd00 (by decide)) rip input.rsp
  have entry0 : u0.RIP = 0x10dd00 := effect.rip.trans targetEq
  obtain ⟨u, stateU, entry, runU, thunkFrame⟩ := compress512_thunk ctx stateU0 entry0
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
  have returnU : (returnBoundary u).rip = v.pc (pc + 5) form := by
    change memLoad u.external (stackPtr u) 64 = _
    rw [show stackPtr u = stackPtr u0 from thunkFrame.read (n := 64) (r := 4) (by simp),
      thunkFrame.external (by simp [Component.Covers])]
    exact returnU0.trans (Variant.pc_add v pc 5 form)
  have rdiU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans rdi
  have rsiU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form) :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans rsi
  have rdxU : u.regValue .rdx = BitVec.ofNat 64 1 :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans count
  have pre := callee_pre_of_stack ctx stateU (layout form) entry rspU rsiU rdiU
    (by
      rw [returnU]
      exact inProgram_of_textOffset (v.textOffset form + (pc + 5)) site.2.2.2)
  have wordsU : HashStateAt u (u.regValue .rdi) hash := by
    rw [rdiU]
    apply hashState_of_bytes input.hashWords
    intro i hi
    apply callFrame.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covers
    · obtain ⟨j, hj, eq⟩ := covers
      apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.frameBytes + 8)) (len₁ := 8) (c₂ := -BitVec.ofNat 64 form.finalMemory.hash) (len₂ := 64)
        (call_hash_apart form) (stackPtr initial) hj hi (by decide +kernel)
      simpa only [BitVec.sub_eq_add_neg] using eq.symm
    · exact covers
  have budget : form.stackBytes = form.frameBytes + 552 := fb.2.2.1
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have spNat : (stackPtr u).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) := by
    rw [rspU]
    exact Dispatch.stack_sub_toNat512 ctx fb.1
  have compressionPre : CompressionPre u (returnBoundary initial) hash
      chunk 1 := {
    toCalleePre := pre
    countRegister := rdxU
    inputBytes := by
      change (⟨(u.regValue .rsi).toNat, 128⟩ : MemoryRegion).HasBytes u.external chunk
      rw [rsiU]
      refine ⟨bytes.1, fun i => ?_⟩
      have byte := bytes.2 i
      change u.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form)).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [callFrame.byte (x := stackPtr initial - BitVec.ofNat 64 (copyOutputOffset form) + BitVec.ofNat 64 i.val) ?_]
      · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
      · intro c hc covers
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact covers
        · obtain ⟨j, hj, eq⟩ := covers
          apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.frameBytes + 8)) (len₁ := 8) (c₂ := -BitVec.ofNat 64 (copyOutputOffset form)) (len₂ := 128)
            (call_input_apart form) (stackPtr initial) hj
            (show i.val < 128 from by have hsize : chunk.size = 128 := bytes.1; omega) (by decide +kernel)
          simpa only [BitVec.sub_eq_add_neg] using eq.symm
        · exact covers
    hashWords := wordsU
  }
  obtain ⟨t, result⟩ := compression_correct_of_block body compressionPre (by
    rw [returnU]
    exact inProgram_of_textOffset (v.textOffset form + (pc + 5)) site.2.2.2)
  have stateT := stateU.of_callee (outputOffset := form.finalMemory.hash) ctx result.toCalleeResult rspU rdiU
    fb.2.2.2.1 fb.2.2.2.2 (by decide +kernel)
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
      Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 424) fb.2.1
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
      (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash).toNat, 64⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 424)).toNat, 424⟩ : MemoryRegion)] := by
    apply memoryWriteFrame_trans (callFrame.memoryWriteFrame ?_) ?_
    · intro c hc a covers
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · obtain ⟨i, hi, rfl⟩ := covers
        refine ⟨⟨(stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat,424⟩, by simp, ?_⟩
        have low : (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat = (stackPtr initial).toNat-(form.frameBytes + 424) :=
          Dispatch.stack_sub_toNat512 ctx (offset := form.frameBytes + 424) fb.2.1
        have slotNat : (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 8)).toNat = (stackPtr initial).toNat-(form.frameBytes + 8) :=
          Dispatch.stack_sub_toNat512 ctx fb.1
        change (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat ≤ _ ∧ _ < (stackPtr initial-BitVec.ofNat 64 (form.frameBytes + 424)).toNat+424
        rw [low, BitVec.toNat_add, slotNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        constructor <;> omega
      · exact covers.elim
    · simpa only [stackRegion, registerRegion, rdiU] using result.frame
  have outLow : form.finalMemory.hash ≤ form.frameBytes := fb.2.2.2.2
  have outHigh : 64 ≤ form.finalMemory.hash := by have := fb.2.2.2.1; omega
  have reserveLow : form.frameBytes ≤ form.frameBytes + 424 := by omega
  have reserveHigh : form.frameBytes + 424 ≤ form.stackBytes := fb.2.1
  have unchanged {offset len : Nat} (low : offset ≤ form.frameBytes) (high : len ≤ offset)
      (apart : form.finalMemory.hash + len ≤ offset ∨ offset + 64 ≤ form.finalMemory.hash) :=
    frame_bytes (reserve := form.frameBytes + 424) ctx
      (by simpa only [Nat.add_sub_cancel_left] using frame)
      outLow outHigh reserveLow reserveHigh low high apart
  have preserved := preserved_of_bytes input.toPreserved stateT (by
    cases form with
    | slices =>
      intro a ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact frame_bytes ctx frame (offset := 624) (len := 24)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (.inl (by decide)) i hi
    | digest => trivial
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      intro offset member a ha
      obtain ⟨i, hi, rfl⟩ := ha
      have bound := preserved_slot_bounds _ rfl offset member
      exact unchanged bound.1 bound.2.1 bound.2.2 i hi)
    (by intro h; exact abi.1 .rbx (by simp))
    (by intro h; subst form; exact .inl (abi.1 _ (by cases v <;> simp)))
  obtain ⟨fuel, run⟩ := result.execution
  have localFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
    apply memoryWriteFrame_trans (call_stack_frame ctx effect input.rsp)
    apply memoryWriteFrame_trans (thunkFrame.memoryWriteFrame (by
      intro c hc a ha
      have eq : c = .rip := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hc
      subst c
      exact ha.elim))
    exact callee_stack_frame ctx result.toCalleeResult rspU rdiU
      fb.2.2.2.1 fb.2.2.2.2 (by decide)
  refine ⟨1 + 1 + fuel, t, ⟨preserved, ?_, hashPointerState_of_abi input.hashPointer abi⟩,
    ?_, abi, (runU0.trans runU).trans run, localFrame, frame⟩
  · simpa only [rdiU, compressBlocks_single hash chunk bytes.1, BitVec.ofNat_eq_ofNat] using result.hashWords
  · rw [result.rip, returnU, rip]
    exact (Variant.pc_add v pc 5 form).symm

end Sha2.Proofs.Wrapper512.Hash.Finalize.Compress
