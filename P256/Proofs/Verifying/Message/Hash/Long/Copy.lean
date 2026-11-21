import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Input
import P256.Proofs.Program.Frame
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.FieldCall.Result
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem input_byte [Bindings] {initial t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    (pre : Message.Pre initial boundary message)
    (frame : MemoryWriteFrame initial t #v[Stack.region initial 9992])
    {i : Nat} (hi : i < message.size) :
    t.external[memLoad initial.external (initial.regValue .rdx) 64 + BitVec.ofNat 64 i]? =
      initial.external[memLoad initial.external (initial.regValue .rdx) 64 +
        BitVec.ofNat 64 i]? := by
  apply frame_read frame (region := messageRegion initial message) _
    (memoryRegion_contains_add pre.messageBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  intro region member
  have eq : region = Stack.region initial 9992 := by simpa using member
  subst region
  exact pre.messageStack

theorem callee_pre [Bindings] {initial t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {sourceOffset count outputOffset : Nat}
    (pre : Message.Pre initial boundary message)
    (frame : ScalarFrame.FrameState initial t 24 9992 1184)
    (span : sourceOffset + count ≤ message.size)
    (outputAbove : outputOffset ≤ 1176) (outputEnd : count + 48 ≤ outputOffset)
    (source : t.regValue .rsi =
      memLoad initial.external (initial.regValue .rdx) 64 + BitVec.ofNat 64 sourceOffset)
    (destination : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (rip : t.RIP = 0x11c930) (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary 0x11c930 count count 0 := by
  have bounded :
      (memLoad initial.external (initial.regValue .rdx) 64).toNat + message.size < 2^32 :=
    pre.messageBounded
  have offset : (t.regValue .rsi).toNat =
      (memLoad initial.external (initial.regValue .rdx) 64).toNat + sourceOffset := by
    rw [source]
    exact toNat_add_ofNat _ _ (by omega)
  have sub : ∀ a, (registerRegion t .rsi count).Contains a →
      (messageRegion initial message).Contains a := by
    intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + count at ha
    rw [offset] at ha
    change (memLoad initial.external (initial.regValue .rdx) 64).toNat ≤ a ∧
      a < (memLoad initial.external (initial.regValue .rdx) 64).toNat + message.size
    constructor <;> omega
  apply CalleePre.of_disjoint_input_and_stack
    ⟨1184,outputOffset,by decide,by decide,by omega,by omega⟩ pre.stack
    (pre.avoids _ (by simp)) frame.bindingsSupported frame.machine frame.directionFlag frame.loaded
    rip frame.rsp _ _ _ destination frame.allocated pre.outerBoundary ret
  · change (t.regValue .rsi).toNat + count < 2^32
    rw [offset]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (frame.allocated a
      (Option.isSome_iff_exists.mpr
        (hasBytes_allocated (pre.messageBytes) a (sub a.toNat ha))))
  · intro a ha hb
    exact pre.messageStack a (sub a ha) hb


structure Result [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (count destinationOffset : Nat) (ret address : BitVec 64) : Prop extends
    ScalarFrame.FrameState initial t 24 9992 1176 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = ret
  calleeSaved : CalleeSavedRegistersUnchanged s t
  writes : MemoryWriteFrame s t #v[ScalarFrame.workRegion initial 9992]
  copyWrites : MemoryWriteFrame s t #v[
    MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat count,
    MemoryRegion.mk ((stackPtr initial).toNat - 1184) 8]
  copied : ∀ i < count,
    t.external[stackPtr initial - BitVec.ofNat 64 destinationOffset + BitVec.ofNat 64 i]? =
      s.external[address + BitVec.ofNat 64 i]?

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray}
    {sourceOffset count outputOffset : Nat}
    (pre : Message.Pre initial boundary message)
    (frame : Frame initial s)
    (stackFrame : MemoryWriteFrame initial s #v[Stack.region initial 9992])
    (span : sourceOffset + count ≤ message.size)
    (outputAbove : outputOffset ≤ 1176) (outputEnd : count + 48 ≤ outputOffset)
    (offset : Nat) (disp : BitVec 32) (size : offset + 6 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip disp))
    (slot : Extracted.textAddress + BitVec.ofNat 64 offset + 6 + disp.signExtend 64 = 0x2044f8)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi =
      memLoad initial.external (initial.regValue .rdx) 64 + BitVec.ofNat 64 sourceOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (countRegister : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, Result initial s t boundary count outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6)
      (memLoad initial.external (initial.regValue .rdx) 64 + BitVec.ofNat 64 sourceOffset) := by
  have small : count < 2^32 := by
    have bound :
        (memLoad initial.external (initial.regValue .rdx) 64).toNat + message.size < 2^32 :=
      pre.messageBounded
    omega
  have pointer := P256.Proofs.Program.memcpy_pointer frame.loaded
  have target :
      callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip disp) s = 0x11c930 := by
    change (Operand.mem (Extracted.textAddress + BitVec.ofNat 64 offset + 6 +
      disp.signExtend 64) : Operand 64).read s = _
    rw [slot]
    exact pointer.2
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [ScalarFrame.scalar_call_address frame]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide))
      frame.allocated
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) 6 := by
    rw [ScalarFrame.scalar_call_address frame]
    intro i hi j hj he
    apply pre.avoids (Stack.region initial 9992) (by simp)
      (stackPtr initial - 1184 + BitVec.ofNat 64 i)
    · exact ScalarFrame.stack_contains pre.toCalleePre (offset := 1184) (len := 8)
        (by decide) (by decide) ⟨i, hi, rfl⟩
    · left
      change stackPtr initial - 1184 + BitVec.ofNat 64 i = _ at he
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
  have run : Advances boundary 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have callFrame := frame.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have callMemory : MemoryWriteFrame s call #v[ScalarFrame.workRegion initial 9992] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨ScalarFrame.workRegion initial 9992, by simp, ?_⟩
      rw [ScalarFrame.scalar_call_address frame] at ha
      exact ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha
    · exact ha.elim
  have sourceCall : call.regValue .rsi =
      memLoad initial.external (initial.regValue .rdx) 64 + BitVec.ofNat 64 sourceOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationCall : call.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countCall : call.regValue .rdx = BitVec.ofNat 64 count :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans countRegister
  have callPre : CalleePre call boundary 0x11c930 count count 0 :=
    callee_pre pre callFrame span outputAbove outputEnd sourceCall destinationCall entry (by
      change InProgram (stackTop call)
      rw [(callEffect_stack effect).1]
      change InProgram (Extracted.textAddress + BitVec.ofNat 64 offset + 6)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        inProgram_of_textOffset (offset + 6) size)
  obtain ⟨t, result, copied, _⟩ := P256.Proofs.Program.memcpy_correct callPre countCall small
  have copyMemory := result.stack_frame (savedBytes := 48) pre.stack callFrame.rsp
    destinationCall (by decide) (by decide) (by omega) outputEnd
  have frameT : ScalarFrame.FrameState initial t 24 9992 1176 :=
    FieldCall.after_result pre.toCalleePre callFrame result (by decide) copyMemory
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
  have stackNat : (stackPtr call).toNat = (stackPtr initial).toNat - 1184 := by
    rw [callFrame.rsp]
    exact stack_sub_toNat pre.stack (offset := 1184) (by decide)
  have stackRegion : Stack.region call 0 =
      MemoryRegion.mk ((stackPtr initial).toNat - 1184) 8 := by
    change MemoryRegion.mk (stackPtr call).toNat
      ((stackPtr call).toNat + 8 - (stackPtr call).toNat) = _
    rw [Nat.add_sub_cancel_left, stackNat]
  have copyWrites : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat count,
      MemoryRegion.mk ((stackPtr initial).toNat - 1184) 8] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - 1184) 8, by simp, ?_⟩
        rw [ScalarFrame.scalar_call_address frame]
        have base := stack_sub_toNat pre.stack (show 1184 ≤ 9992 by omega)
        rw [toNat_add_ofNat _ _ (by rw [base]; omega), base]
        change (stackPtr initial).toNat - 1184 ≤ _ ∧
          _ < (stackPtr initial).toNat - 1184 + 8
        constructor <;> omega
      · exact covered.elim
    · simpa only [stackRegion, registerRegion, destinationCall] using result.frame
  obtain ⟨fuel, copyRun⟩ := result.execution
  refine ⟨t, frameT, ⟨1 + fuel, run.trans copyRun⟩,
    result.rip.trans (callEffect_stack effect).1, calleeSaved,
    memoryWriteFrame_trans callMemory copyMemory, copyWrites, ?_⟩
  intro i hi
  have byte := copied i hi
  rw [destinationCall, sourceCall] at byte
  have callByte := input_byte pre
    (memoryWriteFrame_trans stackFrame (work_frame_stack pre.toCalleePre callMemory))
    (i := sourceOffset + i) (by omega)
  have oldByte := input_byte pre stackFrame (i := sourceOffset + i) (by omega)
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at byte ⊢
  exact byte.trans (callByte.trans oldByte.symm)

theorem Result.stack_byte [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {ret address : BitVec 64} {message : ByteArray}
    {count destinationOffset offset len : Nat}
    (pre : Message.Pre initial boundary message)
    (result : Result initial s t boundary count destinationOffset ret address)
    (destinationBound : destinationOffset ≤ 9992)
    (bound : offset ≤ 1176) (span : len ≤ offset + 8)
    (apart : destinationOffset + len ≤ offset ∨ offset + count ≤ destinationOffset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have sub := stack_sub_toNat pre.stack (show offset ≤ 9992 by omega)
  have destinationSub := stack_sub_toNat pre.stack destinationBound
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [toNat_add_ofNat _ _ (by rw [sub]; omega), sub]
  apply result.copyWrites
  intro region member inside
  have cases : region =
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat count ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 1184) 8 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 destinationOffset).toNat + count at inside
    rw [destinationSub, address] at inside
    omega
  · change (stackPtr initial).toNat - 1184 ≤ _ ∧
      _ < (stackPtr initial).toNat - 1184 + 8 at inside
    rw [address] at inside
    omega

end P256.Proofs.Verifying.Message.Hash.Long.Copy
