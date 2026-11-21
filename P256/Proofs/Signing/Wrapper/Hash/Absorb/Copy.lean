import P256.Proofs.Signing.Wrapper.Hash.Initial
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Input
import P256.Proofs.Program.Frame
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.FieldCall.Result
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem input_byte [Bindings] {initial start t : RamState}
    {secret message : ByteArray} {offset : Nat}
    (pre : HashEntry initial start secret message)
    (frame : Frame initial start t offset)
    {i : Nat} (hi : i < message.size) :
    t.external[memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 i]? =
      initial.external[memLoad initial.external (initial.regValue .rdi + 8) 64 +
        BitVec.ofNat 64 i]? := by
  obtain ⟨slices, call⟩ := pre.context.call
  apply frame_read frame.frame (region := messageRegion initial message)
    (wrapper_read_disjoint call (Entry.HashCall.message_input_region call))
    (memoryRegion_contains_add (message_input pre frame).1 (Nat.le_refl _) (Nat.le_refl _) hi)


theorem callee_pre [Bindings] {initial start t : RamState}
    {secret message : ByteArray} {sourceOffset count outputOffset : Nat}
    (pre : HashEntry initial start secret message)
    (frame : Frame initial start t 528)
    (span : sourceOffset + count ≤ message.size)
    (outputAbove : outputOffset ≤ 520) (outputEnd : count + 240 ≤ outputOffset)
    (source : t.regValue .rsi =
      memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 sourceOffset)
    (destination : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (rip : t.RIP = 0x11c930) (ret : InProgram (returnBoundary t).rip) :
    CalleePre t (returnBoundary initial) 0x11c930 count count 0 := by
  have bounded :
      (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + message.size < 2^32 :=
    (message_input pre frame).1
  have offset : (t.regValue .rsi).toNat =
      (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + sourceOffset := by
    rw [source]
    exact toNat_add_ofNat _ _ (by omega)
  have sub : ∀ a, (registerRegion t .rsi count).Contains a →
      (messageRegion initial message).Contains a := by
    intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + count at ha
    rw [offset] at ha
    change (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat ≤ a ∧
      a < (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + message.size
    constructor <;> omega
  apply CalleePre.of_disjoint_input_and_stack
    ⟨528,outputOffset,by decide,by decide,by omega,by omega⟩ (stack pre.context)
    (stack_avoids pre.context) frame.bindingsSupported frame.machine frame.directionFlag frame.loaded
    rip frame.rsp _ _ _ destination frame.allocated (outside pre.context) ret
  · change (t.regValue .rsi).toNat + count < 2^32
    rw [offset]
    omega
  · intro a ha
    exact hasBytes_allocated (message_input pre frame).2.1 a (sub a.toNat ha)
  · intro a ha hb
    exact (message_input pre frame).2.2 a (sub a ha) hb


structure Result [Bindings] (initial start s t : RamState)
    (count destinationOffset : Nat) (ret address : BitVec 64) : Prop extends
    Frame initial start t where
  copyRun : ∃ fuel, Advances (returnBoundary initial) fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  copyWrites : MemoryWriteFrame s t #v[
    MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat count,
    MemoryRegion.mk ((stackPtr initial).toNat - 528) 8]
  copied : ∀ i < count,
    t.external[stackPtr initial - BitVec.ofNat 64 destinationOffset + BitVec.ofNat 64 i]? =
      s.external[address + BitVec.ofNat 64 i]?

theorem copy [Bindings] {initial start s : RamState}
    {secret message : ByteArray}
    {sourceOffset count outputOffset : Nat}
    (pre : HashEntry initial start secret message)
    (frame : Frame initial start s)
    (span : sourceOffset + count ≤ message.size)
    (outputAbove : outputOffset ≤ 520) (outputEnd : count + 240 ≤ outputOffset)
    (offset : Nat) (disp : BitVec 32) (size : offset + 6 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip disp))
    (slot : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64 = 0x2044f8)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi =
      memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 sourceOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (countRegister : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, Result initial start s t count outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6)
      (memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 sourceOffset) := by
  have push : pushAddr s = stackPtr initial - 528 := by
    change stackPtr s - 8 = _
    rw [frame.rsp]
    bv_omega
  have small : count < 2^32 := by
    have bound :
        (memLoad initial.external (initial.regValue .rdi + 8) 64).toNat + message.size < 2^32 :=
      (message_input pre frame).1
    omega
  have pointer := P256.Proofs.Program.memcpy_pointer frame.loaded
  have target :
      callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip disp) s = 0x11c930 := by
    change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 +
      disp.signExtend 64) : Operand 64).read s = _
    rw [slot]
    exact pointer.2
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 (stack pre.context)
        (fun a ha hp => stack_avoids pre.context a ha (.inr hp)) (by decide) (by decide))
      frame.allocated
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) 6 := by
    rw [push]
    intro i hi j hj he
    apply stack_avoids pre.context
      (stackPtr initial - 528 + BitVec.ofNat 64 i)
    · exact stack_buffer_contains (stack pre.context) (offset := 528) (len := 8)
        (by decide) (by decide) (memoryRegion_contains_add
          (stack_buffer_bounded (stack pre.context) (by decide) (by decide))
          (Nat.le_refl _) (Nat.le_refl _) hi)
    · left
      change stackPtr initial - 528 + BitVec.ofNat 64 i = _ at he
      rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (offset + j) (by omega)
  have pointerReadable : MemReadable s
      ((AddrMode.rip disp).addr s (Extracted.textAddress + BitVec.ofNat 64 offset + 6)) 8 := by
    change MemReadable s (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64) 8
    rw [slot]
    exact pointer.1
  obtain ⟨call, step, ready, effect⟩ :=
    call_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip disp)
      trivial rfl rfl s (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) offset _
        (by change offset + 6 ≤ 118431; omega) bytes)
      ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointerReadable⟩
  have entry : call.RIP = 0x11c930 := effect.rip.trans target
  have run : Advances (returnBoundary initial) 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program (outside pre.context) (inProgram_of_textOffset 0x1c930 (by decide))))
  have callFrame : Frame initial start call 528 :=
    frame.after_effect pre.context run ready effect.agrees
      (by
        intro c hc a ha
        simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact ha.elim
        · refine ⟨workRegion initial, by simp, ?_⟩
          rw [push] at ha
          exact work_contains pre.context (by decide) (by decide) ha
        · exact ha.elim)
      (effect.writes.1.trans push) (by simp)
  have sourceCall : call.regValue .rsi =
      memLoad initial.external (initial.regValue .rdi + 8) 64 + BitVec.ofNat 64 sourceOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationCall : call.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countCall : call.regValue .rdx = BitVec.ofNat 64 count :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans countRegister
  have callPre : CalleePre call (returnBoundary initial) 0x11c930 count count 0 :=
    callee_pre pre callFrame span outputAbove outputEnd sourceCall destinationCall entry (by
      change InProgram (stackTop call)
      rw [(callEffect_stack effect).1]
      change InProgram (Extracted.textAddress + BitVec.ofNat 64 offset + 6)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        inProgram_of_textOffset (offset + 6) size)
  obtain ⟨t, result, copied, _⟩ := P256.Proofs.Program.memcpy_correct callPre countCall small
  have frameT : Frame initial start t :=
    callFrame.after_callee pre.context result destinationCall (by decide) (by decide)
      (by omega) outputEnd
  have calleeSaved : CalleeSavedRegistersUnchanged s t := by
    intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have bounds := stack_bounds (stack pre.context)
  have stackNat : (stackPtr call).toNat = (stackPtr initial).toNat - 528 := by
    rw [callFrame.rsp]
    exact stack_sub_toNat (stack pre.context) (offset := 528) (by decide)
  have stackRegion : Stack.region call 0 =
      MemoryRegion.mk ((stackPtr initial).toNat - 528) 8 := by
    change MemoryRegion.mk (stackPtr call).toNat
      ((stackPtr call).toNat + 8 - (stackPtr call).toNat) = _
    rw [Nat.add_sub_cancel_left, stackNat]
  have copyWrites : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat count,
      MemoryRegion.mk ((stackPtr initial).toNat - 528) 8] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - 528) 8, by simp, ?_⟩
        rw [push]
        have base : (stackPtr initial - 528).toNat = (stackPtr initial).toNat - 528 :=
          stack_sub_toNat (stack pre.context) (show 528 ≤ 5112 by omega)
        rw [toNat_add_ofNat _ _ (by rw [base]; omega), base]
        change (stackPtr initial).toNat - 528 ≤ _ ∧
          _ < (stackPtr initial).toNat - 528 + 8
        constructor <;> omega
      · exact covered.elim
    · simpa only [stackRegion, registerRegion, destinationCall] using result.frame
  obtain ⟨fuel, copyRun⟩ := result.execution
  refine ⟨t, frameT, ⟨1 + fuel, run.trans copyRun⟩,
    result.rip.trans (callEffect_stack effect).1, calleeSaved,
    copyWrites, ?_⟩
  intro i hi
  have byte := copied i hi
  rw [destinationCall, sourceCall] at byte
  have callByte := input_byte pre callFrame
    (i := sourceOffset + i) (by omega)
  have oldByte := input_byte pre frame (i := sourceOffset + i) (by omega)
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at byte ⊢
  exact byte.trans (callByte.trans oldByte.symm)

theorem Result.stack_byte [Bindings] {initial start s t : RamState}
    {ret address : BitVec 64} {secret message : ByteArray}
    {count destinationOffset offset len : Nat}
    (pre : HashEntry initial start secret message)
    (result : Result initial start s t count destinationOffset ret address)
    (destinationBound : destinationOffset ≤ 5112)
    (bound : offset ≤ 520) (span : len ≤ offset + 8)
    (apart : destinationOffset + len ≤ offset ∨ offset + count ≤ destinationOffset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds (stack pre.context)
  have sub := stack_sub_toNat (stack pre.context) (show offset ≤ 5112 by omega)
  have destinationSub := stack_sub_toNat (stack pre.context) destinationBound
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [toNat_add_ofNat _ _ (by rw [sub]; omega), sub]
  apply result.copyWrites
  intro region member inside
  have cases : region =
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat count ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 528) 8 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat + count at inside
    rw [destinationSub, address] at inside
    omega
  · change (stackPtr initial).toNat - 528 ≤ _ ∧
      _ < (stackPtr initial).toNat - 528 + 8 at inside
    rw [address] at inside
    omega

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Copy
