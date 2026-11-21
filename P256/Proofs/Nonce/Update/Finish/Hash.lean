import P256.Proofs.Nonce.Update.Finish.HashPre
import P256.Proofs.HMAC.Finalize

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure HmacCallResult [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (reserve depth stateOffset outputOffset : Nat) (ret : BitVec 64) (key : ByteArray)
    (input : ByteArray) : Prop extends ScalarFrame.FrameState initial t 64 reserve (BitVec.ofNat 64 depth) where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  writes : MemoryWriteFrame s t #v[
    MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 stateOffset).toNat 168,
    MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 32,
    MemoryRegion.mk ((stackPtr initial).toNat - (depth + 680)) 680]
  drbg : ∀ i < 64, t.external[initial.regValue .rdi + BitVec.ofNat 64 i]? =
    s.external[initial.regValue .rdi + BitVec.ofNat 64 i]?
  output : (MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 32).HasBytes
    t.external (Standards.RFC.HMAC.hmac Operations.hash 64 key input)

theorem hmac_call [Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {outerEntry : BitVec 64} {reserve depth : Nat}
    {state : State} {key : ByteArray} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary outerEntry reserve state)
    (frame : ScalarFrame.FrameState initial s 64 reserve (BitVec.ofNat 64 depth))
    (layout : StackCallLayout reserve 32 168 672)
    (stackOffset : layout.stackOffset = depth + 8) (saved : 48 ≤ depth)
    (_stateSaved : 216 ≤ layout.outputOffset) (outputSaved : 80 ≤ layout.inputOffset)
    (offset : Nat) (disp : BitVec 32) (size : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x100f10)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (keySize : key.size = 32)
    (inputSize : input.size = 32 ∨ input.size = 33 ∨ input.size = 97)
    (hmac : HMAC.HmacStateAt s
      (stackPtr initial - BitVec.ofNat 64 layout.outputOffset) key input) :
    ∃ t, HmacCallResult initial s t boundary reserve depth layout.outputOffset layout.inputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 5) key input := by
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
    (by rw [target]; exact inProgram_of_textOffset 0xf10 (by decide)) rip
  have entryFrame := frame.after_call pre.callee (by omega) saved ready callEffect
  have rsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 layout.stackOffset := by
    rw [stackOffset]
    exact entryFrame.rsp
  have sourceU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset :=
    (callEffect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset :=
    (callEffect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary u).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 :=
    (callEffect_stack callEffect).1
  have retProgram : InProgram (returnBoundary u).rip := by
    rw [ret]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      inProgram_of_textOffset (offset+5) size
  have frameU : ScalarFrame.FrameState initial u 64 reserve (BitVec.ofNat 64 layout.stackOffset) := by
    rw [stackOffset]
    exact entryFrame
  have callee := hash_pre pre layout frameU (callEffect.rip.trans target)
    sourceU destinationU retProgram
  have finalizePre : HMAC.HmacFinalizePre u boundary key input := {
    toHashCalleePre := callee
    keySize := keySize
    inputSize := inputSize
    state := by
      rw [destinationU]
      exact hmac.copy (fun _ hi => ScalarFrame.scalar_call_byte (by omega) frame callEffect (by omega) outputEnd hi)
  }
  obtain ⟨t, result⟩ := HMAC.hmac_finalize_correct finalizePre
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 depth := by
    exact result.rsp.trans ((callEffect_stack callEffect).2.trans frame.rsp)
  have work : MemoryWriteFrame u t #v[ScalarFrame.workRegion initial reserve] :=
    result.toCalleeResult.stack_frame pre.stack entryFrame.rsp sourceU
      (by omega) (by omega) (by omega) outputSaved
  have afterFrame := frame_after_result pre.callee (by omega) entryFrame result.toCalleeResult
    (by
      intro a ha
      apply work a
      intro r hr hin
      exact ha r (by simpa using Or.inr hr) hin) rspT
  have stackNat : (stackPtr u).toNat = (stackPtr initial).toNat - (depth+8) := by
    rw [entryFrame.rsp, stack_sub_toNat pre.stack (by omega)]
  have stackRegion : Stack.region u 672 =
      MemoryRegion.mk ((stackPtr initial).toNat - (depth+680)) 680 := by
    change MemoryRegion.mk ((stackPtr u).toNat - 672)
      ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 672)) = _
    rw [stackNat]
    have startEq : (stackPtr initial).toNat - (depth+8) - 672 =
        (stackPtr initial).toNat - (depth+680) := by omega
    have sizeEq : (stackPtr initial).toNat - (depth+8) + 8 -
        ((stackPtr initial).toNat - (depth+8) - 672) = 680 := by omega
    rw [sizeEq, startEq]
  have writes : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 layout.outputOffset).toNat 168,
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 layout.inputOffset).toNat 32,
      MemoryRegion.mk ((stackPtr initial).toNat - (depth+680)) 680] := by
    apply memoryWriteFrame_trans (callEffect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - (depth+680)) 680, by simp, ?_⟩
        rw [ScalarFrame.scalar_call_address frame]
        have base := stack_sub_toNat pre.stack (show depth+8 ≤ reserve by omega)
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
          Nat.mod_eq_of_lt (by rw [base]; omega), base]
        change (stackPtr initial).toNat - (depth+680) ≤ _ ∧
          _ < (stackPtr initial).toNat - (depth+680) + 680
        constructor <;> omega
      · exact covered.elim
    · intro a ha
      apply result.frame a
      intro r hr hin
      have cases : r = registerRegion u .rsi 32 ∨ r = Stack.region u 672 := by simpa using hr
      rcases cases with rfl | rfl
      · apply ha (MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 layout.inputOffset).toNat 32) (by simp)
        simpa only [registerRegion, sourceU] using hin
      · apply ha (MemoryRegion.mk ((stackPtr initial).toNat - (depth+680)) 680) (by simp)
        simpa only [stackRegion] using hin
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨t, afterFrame, ⟨1+fuel, callRun.trans run⟩, result.rip.trans ret, ?_, writes, ?_, ?_⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact callEffect.agrees.read (n := 64) (r := 3) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 5) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 12) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 13) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 14) (by simp)
    · exact callEffect.agrees.read (n := 64) (r := 15) (by simp)
  · intro i hi
    have stackWork : MemoryWriteFrame u t #v[Stack.region initial reserve] := by
      intro a ha
      apply work a
      intro r hr hin
      have eq : r = ScalarFrame.workRegion initial reserve := by simpa using hr
      subst r
      apply ha (Stack.region initial reserve) (by simp)
      change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - reserve + (reserve - 48) at hin
      change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
        a.toNat < (Stack.region initial reserve).start + (Stack.region initial reserve).size
      rw [stack_region_end]
      constructor <;> omega
    have totalWork := memoryWriteFrame_trans
      (callEffect.agrees.memoryWriteFrame (ScalarFrame.scalar_call_writes pre.callee (by omega) frame)) stackWork
    apply totalWork
    intro region member inside
    have eq : region = Stack.region initial reserve := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi) inside
  · simpa only [registerRegion, sourceU] using result.outputBytes

end P256.Proofs.Nonce.Update.Finish
