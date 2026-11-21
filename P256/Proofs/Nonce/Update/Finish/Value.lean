import P256.Proofs.Nonce.Update.Finish.ValuePre
import P256.Proofs.Nonce.UpdateValue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure ValueCallResult [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (reserve depth : Nat) (ret : BitVec 64) (state : State) : Prop extends
    ScalarFrame.FrameState initial t 64 reserve (BitVec.ofNat 64 depth) where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  writes : MemoryWriteFrame s t #v[
    registerRegion initial .rdi 64,
    MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176]
  drbg : DrbgAt t (initial.regValue .rdi) (updateValue state)

theorem value_call [Bindings]
    {initial s : RamState} {boundary : ReturnBoundary} {outerEntry : BitVec 64}
    {reserve depth : Nat} {original state : State}
    (pre : DrbgCalleePre initial boundary outerEntry reserve original)
    (frame : ScalarFrame.FrameState initial s 64 reserve (BitVec.ofNat 64 depth))
    (capacity : depth + 1176 ≤ reserve) (aligned : (depth + 8) % 16 = 0) (saved : 48 ≤ depth)
    (offset : Nat) (disp : BitVec 32) (size : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x10a900)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (pointer : s.regValue .rdi = initial.regValue .rdi)
    (drbg : DrbgAt s (initial.regValue .rdi) state) :
    ∃ t, ValueCallResult initial s t boundary reserve depth
      (Extracted.textAddress + BitVec.ofNat 64 offset + 5) state := by
  have bounds := stack_bounds pre.stack
  obtain ⟨u, callRun, ready, effect⟩ := ScalarFrame.scalar_call pre.callee
    (by omega) (by omega) frame offset disp (by omega) bytes
    (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0xa900 (by decide)) rip
  have entryFrame := frame.after_call pre.callee (by omega) saved ready effect
  have pointerU : u.regValue .rdi = initial.regValue .rdi :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans pointer
  have ret : (returnBoundary u).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 :=
    (callEffect_stack effect).1
  have retProgram : InProgram (returnBoundary u).rip := by
    rw [ret]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      inProgram_of_textOffset (offset + 5) size
  have drbgU : DrbgAt u (initial.regValue .rdi) state := by
    apply drbg.of_frame pre.stateBounded
      (effect.agrees.memoryWriteFrame (ScalarFrame.scalar_call_writes pre.callee (by omega) frame))
    intro region member
    have eq : region = Stack.region initial reserve := by simpa using member
    subst region
    exact pre.separation
  have callee : UpdateValuePre u boundary state := nested_pre pre entryFrame
    (by omega) aligned (effect.rip.trans target) pointerU retProgram drbgU
  obtain ⟨t, result⟩ := UpdateValue.correct callee
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 depth :=
    result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp)
  have stackNat : (stackPtr u).toNat = (stackPtr initial).toNat - (depth + 8) := by
    rw [entryFrame.rsp, stack_sub_toNat pre.stack (by omega)]
  have stackRegion : Stack.region u 1168 =
      MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176 := by
    change MemoryRegion.mk ((stackPtr u).toNat - 1168)
      ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 1168)) = _
    rw [stackNat]
    have startEq : (stackPtr initial).toNat - (depth + 8) - 1168 =
        (stackPtr initial).toNat - (depth + 1176) := by omega
    have sizeEq : (stackPtr initial).toNat - (depth + 8) + 8 -
        ((stackPtr initial).toNat - (depth + 8) - 1168) = 1176 := by omega
    rw [sizeEq, startEq]
  have resultWrites : MemoryWriteFrame u t #v[registerRegion initial .rdi 64,
      MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176] := by
    simpa only [stackRegion, registerRegion, pointerU] using result.frame
  have writes : MemoryWriteFrame s t #v[registerRegion initial .rdi 64,
      MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) resultWrites
    intro c member a covered
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · obtain ⟨i, hi, rfl⟩ := covered
      refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176, by simp, ?_⟩
      rw [ScalarFrame.scalar_call_address frame]
      have base := stack_sub_toNat pre.stack (show depth + 8 ≤ reserve by omega)
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
        Nat.mod_eq_of_lt (by rw [base]; omega), base]
      change (stackPtr initial).toNat - (depth + 1176) ≤ _ ∧
        _ < (stackPtr initial).toNat - (depth + 1176) + 1176
      constructor <;> omega
    · exact covered.elim
  have work : MemoryWriteFrame u t
      #v[registerRegion initial .rdi 64, ScalarFrame.workRegion initial reserve] := by
    intro a ha
    apply resultWrites a
    intro region member inside
    have cases : region = registerRegion initial .rdi 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - (depth + 1176)) 1176 := by
      simpa using member
    rcases cases with rfl | rfl
    · exact ha _ (by simp) inside
    · apply ha (ScalarFrame.workRegion initial reserve) (by simp)
      change (stackPtr initial).toNat - (depth + 1176) ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - (depth + 1176) + 1176 at inside
      change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - reserve + (reserve - 48)
      constructor <;> omega
  have afterFrame := frame_after_result pre.callee (by omega) entryFrame
    result.toCalleeResult work rspT
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨t, afterFrame, ⟨1 + fuel, callRun.trans run⟩, result.rip.trans ret, ?_, writes, ?_⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · simpa only [pointerU] using result.stateBytes

end P256.Proofs.Nonce.Update.Finish
