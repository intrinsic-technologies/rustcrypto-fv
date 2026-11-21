import P256.Proofs.Nonce.Update.Frame
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.SHA256

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure CompressionCallResult [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (reserve depth outputOffset : Nat) (ret : BitVec 64) (hash : Array UInt32)
    (input : ByteArray) : Prop extends ScalarFrame.FrameState initial t 64 reserve (BitVec.ofNat 64 depth) where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  writes : MemoryWriteFrame s t #v[
    MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 32,
    MemoryRegion.mk ((stackPtr initial).toNat - (depth + 344)) 344]
  drbg : ∀ i < 64, t.external[initial.regValue .rdi + BitVec.ofNat 64 i]? =
    s.external[initial.regValue .rdi + BitVec.ofNat 64 i]?
  hash : SHA256.HashStateAt t (stackPtr initial - BitVec.ofNat 64 outputOffset)
    (SHA256.compressBlocks hash input)

set_option maxRecDepth 2048 in
theorem compression_call [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {outerEntry : BitVec 64} {reserve depth : Nat}
    {state : State} {hash : Array UInt32} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary outerEntry reserve state)
    (frame : ScalarFrame.FrameState initial s 64 reserve (BitVec.ofNat 64 depth))
    (layout : StackCallLayout reserve 64 32 336)
    (stackOffset : layout.stackOffset = depth + 8) (saved : 48 ≤ depth)
    (outputSaved : 80 ≤ layout.outputOffset) (offset : Nat) (disp : BitVec 32) (size : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x115990)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (count : s.regValue .rdx = 1)
    (inputBytes : (MemoryRegion.mk
      (stackPtr initial - BitVec.ofNat 64 layout.inputOffset).toNat 64).HasBytes s.external input)
    (hashWords : SHA256.HashStateAt s
      (stackPtr initial - BitVec.ofNat 64 layout.outputOffset) hash) :
    ∃ t, CompressionCallResult initial s t boundary reserve depth layout.outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 5) hash input := by
  have bounds := stack_bounds pre.stack
  have capacity := layout.capacity
  have inputAbove := layout.inputAbove
  have outputAbove := layout.outputAbove
  have inputEnd := layout.inputEnd
  have outputEnd := layout.outputEnd
  have align := layout.aligned
  rw [stackOffset] at capacity inputAbove outputAbove align
  have small : depth + 16 < 2^64 := by omega
  obtain ⟨u, callRun, ready, callEffect⟩ := ScalarFrame.scalar_call pre.callee (by omega) (by omega) frame
    offset disp (by omega) bytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0x15990 (by decide)) rip
  have entryFrame := frame.after_call pre.callee (by omega) saved ready callEffect
  have rsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 layout.stackOffset := by
    rw [stackOffset]
    exact entryFrame.rsp
  have sourceU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset :=
    (callEffect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset :=
    (callEffect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countU : u.regValue .rdx = 1 :=
    (callEffect.agrees.read (n := 64) (r := 2) (by simp)).trans count
  have ret : (returnBoundary u).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 :=
    (callEffect_stack callEffect).1
  have retProgram : InProgram (returnBoundary u).rip := by
    rw [ret]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      inProgram_of_textOffset (offset+5) size
  have callee := pre.callee.of_stack layout entryFrame.bindingsSupported entryFrame.machine entryFrame.directionFlag
    entryFrame.loaded entryFrame.allocated (callEffect.rip.trans target) rsp sourceU destinationU retProgram
  have compressionPre : SHA256.CompressionPre u boundary hash input 1 := {
    toCalleePre := callee
    countRegister := countU
    inputBytes := by
      change (MemoryRegion.mk (u.regValue .rsi).toNat 64).HasBytes u.external input
      rw [sourceU]
      exact hasBytes_copy inputBytes (fun _ hi => ScalarFrame.scalar_call_byte (by omega) frame callEffect (by omega) inputEnd hi)
    hashWords := by
      rw [destinationU]
      refine ⟨hashWords.1, ?_⟩
      intro j hj
      apply loadBytes_ok_copy
        (copied_sub (offset := 4*j) (len := 4)
          (fun i hi => ScalarFrame.scalar_call_byte (len := 32) (by omega) frame callEffect
            (by omega) outputEnd hi) (by omega))
      exact hashWords.2 j hj
  }
  obtain ⟨t, result⟩ := SHA256.compression_correct compressionPre
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 depth := by
    exact result.rsp.trans ((callEffect_stack callEffect).2.trans frame.rsp)
  have work := result.toCalleeResult.stack_frame (savedBytes := 48) pre.stack rsp
    destinationU layout.capacity (by omega) (by omega) outputSaved
  have memory : MemoryWriteFrame u t
      #v[registerRegion initial .rdi 64, ScalarFrame.workRegion initial reserve] := by
    intro a ha
    apply work a
    intro region hr
    exact ha region (by simpa using Or.inr hr)
  have afterFrame := Update.frame_after_result pre.callee (by omega) entryFrame
    result.toCalleeResult memory rspT
  have calleeSaved : CalleeSavedRegistersUnchanged s t := by
    intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact callEffect.agrees.read (n := 64) (r := 3) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 5) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 12) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 13) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 14) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 15) (by simp)
  have stackNat : (stackPtr u).toNat = (stackPtr initial).toNat - (depth+8) := by
    rw [entryFrame.rsp, stack_sub_toNat pre.stack (by omega)]
  have stackRegion : Stack.region u 336 =
      MemoryRegion.mk ((stackPtr initial).toNat - (depth+344)) 344 := by
    change MemoryRegion.mk ((stackPtr u).toNat - 336)
      ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)) = _
    rw [stackNat]
    have startEq : (stackPtr initial).toNat - (depth+8) - 336 =
        (stackPtr initial).toNat - (depth+344) := by omega
    have sizeEq : (stackPtr initial).toNat - (depth+8) + 8 -
        ((stackPtr initial).toNat - (depth+8) - 336) = 344 := by omega
    rw [sizeEq, startEq]
  have writes : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 layout.outputOffset).toNat 32,
      MemoryRegion.mk ((stackPtr initial).toNat - (depth+344)) 344] := by
    apply memoryWriteFrame_trans (callEffect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - (depth+344)) 344, by simp, ?_⟩
        rw [ScalarFrame.scalar_call_address frame]
        have base := stack_sub_toNat pre.stack (show depth+8 ≤ reserve by omega)
        rw [toNat_add_ofNat _ _ (by rw [base]; omega), base]
        change (stackPtr initial).toNat - (depth+344) ≤ _ ∧
          _ < (stackPtr initial).toNat - (depth+344) + 344
        constructor <;> omega
      · exact covered.elim
    · simpa only [stackRegion, registerRegion, destinationU] using result.frame
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨t, afterFrame, ⟨1+fuel, callRun.trans run⟩, result.rip.trans ret,
    calleeSaved, writes, ?_, ?_⟩
  · intro i hi
    have callMemory := callEffect.agrees.memoryWriteFrame
      (ScalarFrame.scalar_call_writes pre.callee (by omega) frame)
    have totalWork : MemoryWriteFrame s t #v[Stack.region initial reserve] := by
      apply memoryWriteFrame_trans callMemory
      intro a ha
      apply work a
      intro region hr hin
      have he : region = ScalarFrame.workRegion initial reserve := by simpa using hr
      subst region
      apply ha (Stack.region initial reserve) (by simp)
      change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - reserve + (reserve - 48) at hin
      change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
        a.toNat < (Stack.region initial reserve).start + (Stack.region initial reserve).size
      rw [stack_region_end]
      constructor <;> omega
    apply totalWork
    intro region member inside
    have eq : region = Stack.region initial reserve := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi) inside
  · simpa only [destinationU] using result.hashWords

end P256.Proofs.Nonce
