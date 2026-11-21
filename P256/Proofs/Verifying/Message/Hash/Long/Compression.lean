import P256.Proofs.Verifying.Message.Hash.Long.Prepared
import P256.Proofs.Verifying.Message.Hash.Long.Input
import P256.Proofs.SHA256.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Compressed [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  rip : t.RIP = 0x10d6ce
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  source : t.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64
  length : t.regValue .rbp = BitVec.ofNat 64 message.size
  hash : SHA256.HashStateAt t (frameBase initial + 536)
    (SHA256.compressBlocks SHA256.initialHash message)
  count : loadBytes t.external (frameBase initial + 568) 8 =
    .ok (BitVec.ofNat 64 (message.size / 64))
  savedKey : memLoad t.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad t.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad t.external (frameBase initial + 464) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]

theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Prepared initial s boundary message) :
    ∃ t, Compressed initial t boundary message := by
  obtain ⟨call, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.toFrameState 0xd6c9 0x82c2
    (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x15990 (by decide)) state.rip
  have frame := state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have callWrites := effect.agrees.memoryWriteFrame
    (ScalarFrame.scalar_call_writes pre.toCalleePre (by decide) state.toFrameState)
  have callStack := memoryWriteFrame_trans state.stackFrame callWrites
  have source : call.regValue .rsi = memLoad initial.external (initial.regValue .rdx) 64 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.inputPointer
  have di : call.regValue .rdi = s.regValue .rdi :=
    effect.agrees.read (n := 64) (r := 7) (by simp)
  have destination : call.regValue .rdi = stackPtr initial - 640 := by
    rw [di, state.outputPointer]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have copied {offset len : Nat} (bound : offset ≤ 1176) (span : len ≤ offset + 8)
      {i : Nat} (hi : i < len) :=
    ScalarFrame.scalar_call_byte (frameOffset := 1176) (by decide) state.toFrameState
      effect bound span hi
  have ⟨inputBounded, inputApart, inputBytes⟩ := message_slice pre callStack
    (offset := 0) (count := 64 * (message.size / 64)) (by omega)
  simp only [BitVec.add_zero, Nat.zero_add] at inputBounded inputApart inputBytes
  have cp : SHA256.CompressionPre call boundary SHA256.initialHash
      (SHA256.fullBlocks message) (message.size / 64) := by
    refine ⟨CalleePre.of_disjoint_input_and_stack
      ⟨1184,640,by decide,by decide,by decide,by decide⟩ pre.stack
      (pre.avoids _ (by simp)) frame.bindingsSupported frame.machine frame.directionFlag frame.loaded
      effect.rip frame.rsp ?_ ?_ ?_ destination frame.allocated pre.outerBoundary ?_, ?_, ?_, ?_⟩
    · simpa only [registerRegion, source] using inputBounded
    · simpa only [registerRegion, source] using hasBytes_allocated inputBytes
    · simpa only [registerRegion, source] using inputApart
    · change InProgram (stackTop call)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0xd6ce (by decide)
    · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.countRegister
    · simpa only [registerRegion, source, SHA256.fullBlocks] using inputBytes
    · rw [destination]
      have hash : SHA256.HashStateAt s (stackPtr initial - 640) SHA256.initialHash := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hash
      exact hash.copy (fun i hi => copied (offset := 640) (len := 32) (by decide) (by decide) hi)
  obtain ⟨t, result⟩ := SHA256.compression_correct cp
  have memory := result.toCalleeResult.stack_frame pre.stack frame.rsp destination
    (savedBytes := 48) (by decide) (by decide) (by decide) (by decide)
  have finalFrame := FieldCall.after_result pre.toCalleePre frame result.toCalleeResult
    (frameOffset := 1176) (by decide) memory
  have kept {offset len : Nat} (bound : offset ≤ 1176) (span : len ≤ offset + 8)
      (apart : offset + 32 ≤ 640 ∨ 640 + len ≤ offset) {i : Nat} (hi : i < len) :
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
      (apart : offset + 32 ≤ 640 ∨ 648 ≤ offset) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun o : Option UInt8 => o.getD 0)
      (kept bound (by omega) apart hi)
  refine ⟨t, finalFrame, ?_, result.rip.trans (callEffect_stack effect).1,
    (saved .r13 (by simp)).trans state.current,
    (saved .r12 (by simp)).trans state.endPointer,
    (saved .r14 (by simp)).trans state.source,
    (saved .rbp (by simp)).trans state.length, ?_, ?_, ?_, ?_, ?_,
    memoryWriteFrame_trans callStack (work_frame_stack pre.toCalleePre memory)⟩
  · obtain ⟨before, runBefore⟩ := state.execution
    obtain ⟨fuel, runAfter⟩ := result.execution
    exact ⟨before + 1 + fuel, (runBefore.trans run).trans runAfter⟩
  · have h := result.hashWords
    rw [di, state.outputPointer,
      SHA256.compressBlocks_fullBlocks] at h
    exact h
  · apply loadBytes_ok_copy _ state.count
    intro i hi
    have h := kept (offset := 608) (len := 8) (by decide) (by decide) (by decide) hi
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h
  · have h := word (offset := 720) (by decide) (by decide)
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedKey)
  · have h := word (offset := 792) (by decide) (by decide)
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedOutput)
  · have h := word (offset := 712) (by decide) (by decide)
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h.trans (by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.savedSignature)

end P256.Proofs.Verifying.Message.Hash.Long
