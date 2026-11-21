import P256.Proofs.Nonce.Update.Zero.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.Copy
import P256.Proofs.HMAC.Key.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure CopyCallResult [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (count sourceOffset destinationOffset : Nat) (ret : BitVec 64) : Prop extends
    ScalarFrame.FrameState initial t 64 1856 680 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  writes : MemoryWriteFrame s t #v[ScalarFrame.workRegion initial 1856]
  preserved : ∀ offset len, offset ≤ 680 → len ≤ offset + 8 →
    (destinationOffset + len ≤ offset ∨ offset + count ≤ destinationOffset) → ∀ i < len,
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?
  copied : ∀ i < count,
    t.external[stackPtr initial - BitVec.ofNat 64 destinationOffset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 sourceOffset + BitVec.ofNat 64 i]?

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {count : Nat}

theorem memcpy_call (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (frame : ScalarFrame.FrameState initial s 64 1856 680)
    (layout : StackCallLayout 1856 count count 0)
    (stackOffset : layout.stackOffset = 688)
    (outputSaved : count + 48 ≤ layout.outputOffset) (small : count < 2^32)
    (offset : Nat) (disp : BitVec 32) (size : offset + 6 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip disp))
    (slot : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64 = 0x2044f8)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (countRegister : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, CopyCallResult initial s t boundary count layout.inputOffset layout.outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6) := by
  have inputAbove := layout.inputAbove
  have outputAbove := layout.outputAbove
  rw [stackOffset] at inputAbove outputAbove
  have pointer := memcpy_pointer frame.loaded
  have target : callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip disp) s = 0x11c930 := by
    change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64) : Operand 64).read s = _
    rw [slot]
    exact pointer.2
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [ScalarFrame.scalar_call_address frame]
    exact writable_of_grow (stack_sub_writable8 pre.stack
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
  have sourceCall : call.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationCall : call.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countCall : call.regValue .rdx = BitVec.ofNat 64 count :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans countRegister
  have callPre : CalleePre call boundary 0x11c930 count count 0 :=
    pre.callee.of_stack layout callFrame.bindingsSupported callFrame.machine callFrame.directionFlag
      callFrame.loaded callFrame.allocated entry (by rw [stackOffset]; exact callFrame.rsp)
      sourceCall destinationCall (by
        change InProgram (stackTop call)
        rw [(callEffect_stack effect).1]
        change InProgram (Extracted.textAddress + BitVec.ofNat 64 offset + 6)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
          inProgram_of_textOffset (offset + 6) size)
  obtain ⟨t, result, copied, _⟩ := memcpy_correct callPre countCall small
  have copyMemory := result.stack_frame (savedBytes := 48) pre.stack callFrame.rsp
    destinationCall (by decide) (by decide) (by omega) outputSaved
  have frameT := Update.frame_after_result pre.callee (by decide) callFrame result
    (by
      intro a ha
      apply copyMemory a
      intro r hr
      exact ha r (by simpa using Or.inr hr))
    (result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp))
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
  obtain ⟨fuel, copyRun⟩ := result.execution
  refine ⟨t, frameT, ⟨1 + fuel, run.trans copyRun⟩,
    result.rip.trans (callEffect_stack effect).1, ?_, memoryWriteFrame_trans callMemory copyMemory, ?_, ?_⟩
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
  · intro off len bound span apart i hi
    exact (result_stack_byte (stackOffset := 688) (offset := off) (len := len) pre result callFrame.rsp destinationCall (by decide)
      (by omega) (by omega) (by omega) apart hi span).trans
      (ScalarFrame.scalar_call_byte (frameOffset := 680) (by decide) frame effect bound span hi)
  · intro i hi
    have byte := copied i hi
    rw [destinationCall, sourceCall] at byte
    exact byte.trans (ScalarFrame.scalar_call_byte (frameOffset := 680) (by decide) frame effect
      (by omega) layout.inputEnd hi)

end P256.Proofs.Nonce.Update.Zero
