import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Frame
import Hkdf.Proofs.Common.SHA256.Correctness

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Pads

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def hashOffset (outer : Bool) : Nat := if outer then 416 else 456

private def callPc (outer : Bool) : BitVec 64 := if outer then 0x10fbba else 0x10fb5f

private def displacement (outer : Bool) : BitVec 32 :=
  if outer then 0xffff9a01 else 0xffff9a5c

private def returnPc (outer : Bool) : BitVec 64 :=
  if outer then 0x10fbbf else 0x10fb64

private def layout (outer : Bool) : StackCallLayout 2264 64 32 336 :=
  ⟨464, 336, hashOffset outer, by decide, by decide, by decide,
    by cases outer <;> decide, by decide, by cases outer <;> decide,
    by cases outer <;> decide⟩

abbrev compressionRegions (initial : RamState) (outer : Bool) : Vector MemoryRegion 2 :=
  #v[slotRegion initial (hashOffset outer) 32, slotRegion initial 800 344]

private theorem compression_stack {initial c : RamState}
    (stack : Stack.Valid initial 2264) (rsp : stackPtr c = slot initial 464) :
    Stack.region c 336 = slotRegion initial 800 344 := by
  change (⟨(stackPtr c).toNat - 336,
    (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 336)⟩ : MemoryRegion) = _
  rw [rsp, CallFrame.stack_sub_toNat stack (show 464 ≤ 2264 by decide)]
  change (⟨(stackPtr initial).toNat - 464 - 336,
    (stackPtr initial).toNat - 464 + 8 - ((stackPtr initial).toNat - 464 - 336)⟩
    : MemoryRegion) = ⟨(slot initial 800).toNat, 344⟩
  rw [CallFrame.stack_sub_toNat stack (show 800 ≤ 2264 by decide)]
  have bounds := CallFrame.stack_bounds stack
  have start : (stackPtr initial).toNat - 464 - 336 = (stackPtr initial).toNat - 800 := by omega
  have size : (stackPtr initial).toNat - 464 + 8 - ((stackPtr initial).toNat - 464 - 336) = 344 := by omega
  rw [size, start]

theorem compress [Bindings] (outer : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm block : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (state : Frame initial s boundary)
    (rip : s.RIP = if outer then 0x10fbba else 0x10fb5f)
    (destination : s.regValue .rdi = slot initial (hashOffset outer))
    (source : s.regValue .rsi = slot initial 336)
    (count : s.regValue .rdx = 1)
    (words : HashStateAt s (slot initial (hashOffset outer)) initialHash)
    (bytes : (slotRegion initial 336 64).HasBytes s.external block) :
    ∃ t, Frame initial t boundary ∧ t.RIP = (if outer then 0x10fbbf else 0x10fb64) ∧
      PreservesABI s t ∧ MemoryWriteFrame s t (compressionRegions initial outer) ∧
      HashStateAt t (slot initial (hashOffset outer)) (compressBlocks initialHash block) := by
  have stack := pre.call.stack
  have outside := pre.call.outerBoundary
  have avoid := pre.call.stackAvoid
  have pushAddress : pushAddr s = slot initial 464 := by
    change stackPtr s - 8 = _
    rw [state.rsp]
    unfold base
    rw [BitVec.sub_sub]
    rfl
  have instruction : CodeIn (codeRange (callPc outer) (encodeCallRel32 (displacement outer))) s := by
    cases outer
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xfb5f _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xfbba _
        (by decide) (by decide +kernel)
  have conditions : PushPre (callPc outer) 5 s := by
    refine ⟨rip, ?_, ?_⟩
    · rw [pushAddress]
      exact stack_writable8 stack avoid state.allocated (by decide) (by decide)
    · rw [pushAddress]
      cases outer
      · exact stack_codeApart stack (fun a ha hp ↦ avoid a ha (.inl hp))
          (offset := 464) (codeOffset := 0xfb5f) (by decide) (by decide) (by decide)
      · exact stack_codeApart stack (fun a ha hp ↦ avoid a ha (.inl hp))
          (offset := 464) (codeOffset := 0xfbba) (by decide) (by decide) (by decide)
  have step : StepEffect (PushPre (callPc outer) 5)
      (codeRange (callPc outer) (encodeCallRel32 (displacement outer)))
      (callEffect (fun _ ↦ 0x1095c0) (returnPc outer)) := by
    cases outer
    · exact call_rel32_effect_step 0x10fb5f 0xffff9a5c (by decide +kernel)
    · exact call_rel32_effect_step 0x10fbba 0xffff9a01 (by decide +kernel)
  have writes : WritesWithin (callEffect (fun _ ↦ 0x1095c0) (returnPc outer) s).components
      #v[Stack.region initial 2264] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · rw [pushAddress] at ha
      exact slot_writesWithin stack (by decide) (by decide) ha
    · exact ha.elim
  obtain ⟨c, runningC, called, ret⟩ := state.toRunning.call step instruction conditions
    (boundary_ne_program outside (inProgram_of_textOffset 0x95c0 (by decide))) writes
    (stack_avoids pre)
  have rspC : stackPtr c = slot initial 464 := called.writes.1.trans pushAddress
  have destinationC : c.regValue .rdi = slot initial (hashOffset outer) :=
    (called.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans destination
  have sourceC : c.regValue .rsi = slot initial 336 :=
    (called.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  have countC : c.regValue .rdx = 1 :=
    (called.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans count
  have callee : CalleePre c boundary 0x1095c0 64 32 336 := by
    apply callee_pre_of_stack pre.call.stride stack avoid outside runningC.machine
      runningC.directionFlag runningC.loaded runningC.allocated (layout outer)
      called.rip rspC sourceC destinationC
    rw [ret]
    cases outer
    · exact inProgram_of_textOffset 0xfb64 (by decide)
    · exact inProgram_of_textOffset 0xfbbf (by decide)
  have stackRegion := compression_stack stack rspC
  have pushed : MemoryWriteFrame s c #v[slotRegion initial 800 344] := by
    rw [← stackRegion]
    exact call_frame callee.stack called
  have blockC : (registerRegion c .rsi 64).HasBytes c.external block := by
    rw [registerRegion, sourceC]
    exact frame_hasBytes pushed (by
      intro r hr
      have eq : r = slotRegion initial 800 344 := by simpa only [Vector.mem_singleton] using hr
      rw [eq]
      exact slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide)))
      (slotBound stack (offset := 336) (size := 64) (by decide) (by decide)) bytes
  have hashC : HashStateAt c (c.regValue .rdi) initialHash := by
    rw [destinationC]
    exact hashState_of_bytes words (slot_agrees stack pushed
      (by cases outer <;> decide) (by cases outer <;> decide) (by
      intro r hr
      have eq : r = slotRegion initial 800 344 := by simpa only [Vector.mem_singleton] using hr
      rw [eq]
      exact slotRegion_disjoint stack (by cases outer <;> decide) (by decide)
        (.inl (by cases outer <;> decide))))
  have aligned : (c.regValue .rdi).toNat % 4 = 0 := by
    rw [destinationC, CallFrame.stack_sub_toNat stack (by cases outer <;> decide)]
    have alignment : (stackPtr initial).toNat % 16 = 8 := stack.2.2.2
    have bounds := CallFrame.stack_bounds stack
    cases outer <;> simp only [hashOffset, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have compPre : CompressionPre c boundary initialHash block 1 :=
    ⟨callee, aligned, countC, blockC, hashC⟩
  obtain ⟨t, result⟩ := compression_correct compPre
  have contained := stack_layout_within stack (layout outer) rspC destinationC
  have runningT := runningC.of_callee result.toCalleeResult (by
    intro r hr a ha
    exact ⟨_, by simp, contained r hr a ha⟩)
  obtain ⟨memory, abi⟩ := call_result callee called result.toCalleeResult state.directionFlag
  have footprint : MemoryWriteFrame s t (compressionRegions initial outer) := by
    simpa only [registerRegion, destinationC, stackRegion] using memory
  have rspT : stackPtr t = stackPtr s := result.rsp.trans (congrArg ReturnBoundary.rsp ret)
  have endFrame := state.of_frame stack runningT footprint rspT abi.2.2.1 abi.2.2.2 (by
    intro r hr
    have choice : r = slotRegion initial (hashOffset outer) 32 ∨ r = slotRegion initial 800 344 := by
      simpa only [compressionRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using hr
    have output : base initial + 80 = slot initial 376 := base_add initial (offset := 80) (by decide)
    rw [output]
    rcases choice with rfl | rfl
    · exact ⟨slotRegion_disjoint stack (by decide) (by cases outer <;> decide)
        (.inl (by cases outer <;> decide)),
        slotRegion_disjoint stack (by decide) (by cases outer <;> decide)
        (.inl (by cases outer <;> decide))⟩
    · exact ⟨slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide)),
        slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide))⟩)
  refine ⟨t, endFrame, ?_, abi, footprint, ?_⟩
  · rw [result.rip, ret]
    cases outer <;> rfl
  · simpa only [destinationC] using result.hashWords

end Hkdf.Proofs.NewExpand.Extract.Initialize.Pads
