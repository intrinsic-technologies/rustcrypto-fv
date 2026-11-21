import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Memory
import P256.Proofs.Verifying.Message.Hash.Long.Compression

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 800000 in
theorem call [Bindings] (last : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    {message chunk : ByteArray} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message) (state : HashAt initial s boundary hash)
    (rip : s.RIP = if last then 0x10d8c9 else 0x10d7f0)
    (output : s.regValue .rdi = frameBase initial + 192)
    (source : s.regValue .rsi = frameBase initial) (count : s.regValue .rdx = 1)
    (bytes : (MemoryRegion.mk (frameBase initial).toNat 64).HasBytes s.external chunk) :
    ∃ t, HashAt initial t boundary
      (SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits chunk)) ∧
      t.RIP = s.RIP + 5 ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r) := by
  let pc : Nat := if last then 0xd8c9 else 0xd7f0
  let disp : BitVec 32 := if last then 0x80c2 else 0x819b
  obtain ⟨u, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.toFrameState pc disp
    (by cases last <;> decide) (by cases last <;> decide +kernel)
    (by cases last <;> decide)
    (by cases last <;> exact inProgram_of_textOffset 0x15990 (by decide))
    (by cases last <;> exact rip)
  have frame := state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have callWrites := effect.agrees.memoryWriteFrame
    (ScalarFrame.scalar_call_writes pre.toCalleePre (by decide) state.toFrameState)
  have callStack := memoryWriteFrame_trans state.stackFrame callWrites
  have di : u.regValue .rdi = s.regValue .rdi :=
    effect.agrees.read (n := 64) (r := 7) (by simp)
  have destination : u.regValue .rdi = stackPtr initial - 984 := by
    rw [di, output]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have si : u.regValue .rsi = stackPtr initial - 1176 := by
    have same : u.regValue .rsi = s.regValue .rsi :=
      effect.agrees.read (n := 64) (r := 6) (by simp)
    rw [same, source]
    rfl
  have copied {offset len : Nat} (bound : offset ≤ 1176) (span : len ≤ offset + 8)
      {i : Nat} (hi : i < len) :=
    ScalarFrame.scalar_call_byte (frameOffset := 1176) (by decide) state.toFrameState
      effect bound span hi
  let layout : StackCallLayout 9992 64 32 336 :=
    ⟨1184,1176,984,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : SHA256.CompressionPre u boundary hash chunk 1 := by
    refine ⟨CalleePre.of_stack pre.toCalleePre layout frame.bindingsSupported frame.machine
      frame.directionFlag frame.loaded frame.allocated ?_ frame.rsp si destination ?_, ?_, ?_, ?_⟩
    · cases last <;> exact effect.rip
    · change InProgram (stackTop u)
      rw [(callEffect_stack effect).1]
      cases last
      · exact inProgram_of_textOffset 0xd7f5 (by decide)
      · exact inProgram_of_textOffset 0xd8ce (by decide)
    · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans count
    · change (MemoryRegion.mk (u.regValue .rsi).toNat 64).HasBytes u.external chunk
      rw [si]
      apply hasBytes_copy (a := stackPtr initial - 1176) (b := stackPtr initial - 1176) ?_
        (fun i hi => copied (offset := 1176) (len := 64) (by decide) (by decide) hi)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using bytes
    · rw [destination]
      have hashAt : SHA256.HashStateAt s (stackPtr initial - 984) hash := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hashWords
      exact hashAt.copy (fun i hi => copied (offset := 984) (len := 32) (by decide) (by decide) hi)
  obtain ⟨t, result⟩ := SHA256.compression_correct cp
  have memory := result.toCalleeResult.stack_frame pre.stack frame.rsp destination
    (savedBytes := 48) (by decide) (by decide) (by decide) (by decide)
  have finalFrame := FieldCall.after_result pre.toCalleePre frame result.toCalleeResult
    (frameOffset := 1176) (by decide) memory
  have kept {offset len : Nat} (bound : offset ≤ 1176) (span : len ≤ offset + 8)
      (apart : offset + 32 ≤ 984 ∨ 984 + len ≤ offset) {i : Nat} (hi : i < len) :
      t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    (result.toCalleeResult.stack_byte pre.stack frame.rsp destination
      (by decide) (by decide) bound span apart hi).trans (copied bound span hi)
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have word {offset : Nat} (bound : offset ≤ 1176)
      (apart : offset + 32 ≤ 984 ∨ 992 ≤ offset) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun o : Option UInt8 => o.getD 0) (kept bound (by omega) apart hi)
  have live : Live initial t boundary := by
    refine ⟨finalFrame, ?_, ?_, ?_, ?_, memoryWriteFrame_trans callStack
      (work_frame_stack pre.toCalleePre memory)⟩
    · obtain ⟨before, runBefore⟩ := state.execution
      obtain ⟨fuel, runAfter⟩ := result.execution
      exact ⟨before + 1 + fuel, (runBefore.trans run).trans runAfter⟩
    · have h := word (offset := 720) (by decide) (by decide)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h.trans (by
          simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.savedKey)
    · have h := word (offset := 792) (by decide) (by decide)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h.trans (by
          simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.savedOutput)
    · have h := word (offset := 712) (by decide) (by decide)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h.trans (by
          simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using state.savedSignature)
  refine ⟨t, ⟨live, ?_, (saved .rbx (by simp)).trans state.hashPointer⟩, ?_, saved⟩
  · have h := result.hashWords
    rw [di, output, SHA256.compressBlocks_single hash chunk bytes.1] at h
    exact h
  · have ret : (returnBoundary u).rip =
        Extracted.textAddress + BitVec.ofNat 64 pc + (5 : BitVec 64) :=
      (callEffect_stack effect).1
    rw [result.rip, ret, rip]
    cases last <;> rfl

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
