import P256.Proofs.Nonce.Update.Absorb.SeedCallPre
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Nonce.Update.Absorb.Seeded.Zero.Correct
import P256.Proofs.Nonce.Update.Absorb.SeedCopy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem copy_zero [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original : State} {address : BitVec 64} {outputOffset : Nat}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (frame : FrameState initial s)
    (outputAbove : outputOffset ≤ 680) (outputEnd : 48 ≤ outputOffset)
    (offset : Nat) (disp : BitVec 32) (size : offset + 6 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip disp))
    (slot : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64 = 0x2044f8)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi = address)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (countRegister : s.regValue .rdx = 0) :
    ∃ t, SeedCopyResult initial s t boundary 0 outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6) (address) := by
  have pointer := P256.Proofs.Program.memcpy_pointer frame.loaded
  have target : callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip disp) s = 0x11c930 := by
    change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64) : Operand 64).read s = _
    rw [slot]
    exact pointer.2
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [ScalarFrame.scalar_call_address frame]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) frame.allocated
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) 6 := by
    rw [ScalarFrame.scalar_call_address frame]
    intro i hi j hj he
    apply pre.avoids (Stack.region initial 1856) (by simp)
      (stackPtr initial - 688 + BitVec.ofNat 64 i)
    · exact ScalarFrame.stack_contains pre.callee (offset := 688) (len := 8)
        (by decide) (by decide) ⟨i, hi, rfl⟩
    · left
      change stackPtr initial - 688 + BitVec.ofNat 64 i = _ at he
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
      (programText_slice (programLoaded_codeIn frame.loaded) offset _ (by change offset + 6 ≤ 118431; omega) bytes)
      ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointerReadable⟩
  have entry : call.RIP = 0x11c930 := effect.rip.trans target
  have run : Advances boundary 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have callFrame := frame.after_call pre.callee (by decide) (by decide) ready effect
  have callMemory : MemoryWriteFrame s call #v[ScalarFrame.workRegion initial 1856] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨ScalarFrame.workRegion initial 1856, by simp, ?_⟩
      rw [ScalarFrame.scalar_call_address frame] at ha
      exact ScalarFrame.work_contains pre.callee (by decide) (by decide) ha
    · exact ha.elim
  have sourceCall : call.regValue .rsi = address :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationCall : call.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countCall : call.regValue .rdx = 0 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans countRegister
  have returnRip : (returnBoundary call).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 6 :=
    (callEffect_stack effect).1
  have retIn : InProgram (returnBoundary call).rip := by
    rw [returnRip]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      inProgram_of_textOffset (offset + 6) size
  have stackReadable : MemReadable call (stackPtr call) 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      ScalarFrame.stack_readable pre.callee callFrame (offset := 0) (len := 8) (by decide) (by decide)
  obtain ⟨t, result, _, memory⟩ := Seeded.Zero.memcpy_zero_correct
    (reserve := 0) callFrame.bindingsSupported callFrame.machine callFrame.loaded callFrame.directionFlag entry countCall
    stackReadable (by
      rw [returnRip]
      simp only [Extracted.textAddress]
      bv_omega) pre.outerBoundary (boundary_ne_program pre.outerBoundary retIn)
  have copyMemory := result.stack_frame (savedBytes := 48) pre.stack callFrame.rsp
    destinationCall (by decide) (by decide) (by omega) outputEnd
  have frameT : ScalarFrame.FrameState initial t 64 1856 680 :=
    Update.frame_after_result pre.callee (by decide) callFrame result (by
      intro a ha
      apply copyMemory a
      intro region member inside
      have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
      subst region
      exact ha _ (by simp) inside)
      (result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp))
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
  have bounds := stack_bounds pre.stack
  have stackNat : (stackPtr call).toNat = (stackPtr initial).toNat - 688 := by
    rw [callFrame.rsp]
    exact stack_sub_toNat pre.stack (offset := 688) (by decide)
  have stackRegion : Stack.region call 0 =
      MemoryRegion.mk ((stackPtr initial).toNat - 688) 8 := by
    change MemoryRegion.mk (stackPtr call).toNat
      ((stackPtr call).toNat + 8 - (stackPtr call).toNat) = _
    rw [Nat.add_sub_cancel_left, stackNat]
  have copyWrites : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 0,
      MemoryRegion.mk ((stackPtr initial).toNat - 688) 8] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - 688) 8, by simp, ?_⟩
        rw [ScalarFrame.scalar_call_address frame]
        have base := stack_sub_toNat pre.stack (show 688 ≤ 1856 by omega)
        rw [toNat_add_ofNat _ _ (by rw [base]; omega), base]
        change (stackPtr initial).toNat - 688 ≤ _ ∧
          _ < (stackPtr initial).toNat - 688 + 8
        constructor <;> omega
      · exact covered.elim
    · simpa only [stackRegion, registerRegion, destinationCall] using result.frame
  obtain ⟨fuel, copyRun⟩ := result.execution
  refine ⟨t, frameT, ⟨1 + fuel, run.trans copyRun⟩,
    result.rip.trans (callEffect_stack effect).1, calleeSaved,
    memoryWriteFrame_trans callMemory copyMemory, copyWrites, ?_⟩
  intro i hi
  omega

end P256.Proofs.Nonce.Update.Absorb
