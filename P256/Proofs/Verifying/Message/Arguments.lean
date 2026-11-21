import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.Verifying.Message.SaveArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ArgumentsSaved [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame initial s where
  stackFrame : MemoryWriteFrame initial s #v[Stack.region initial 9992]
  execution : ∃ fuel, Advances boundary fuel initial s
  rip : s.RIP = 0x10d599
  keyPointer : s.regValue .rsi = initial.regValue .rsi
  outputPointer : s.regValue .rdi = initial.regValue .rdi
  descriptors : s.regValue .rdx = initial.regValue .rdx
  count : s.regValue .rcx = initial.regValue .rcx
  signaturePointer : s.regValue .r8 = initial.regValue .r8
  savedKey : memLoad s.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad s.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad s.external (frameBase initial + 464) 64 = initial.regValue .r8

theorem save_arguments_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (rip : s.RIP = 0x10d581) : SaveArgumentsPre s := by
  refine ⟨rip, ?_, ?_⟩
  · intro off hoff
    apply ScalarFrame.stack_writable (frameOffset := 1176) pre state (by decide) _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  · intro off hoff pc len hpc
    apply ScalarFrame.stack_code (frameOffset := 1176) pre state (codeOffset := pc) (by decide) _ hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega

theorem save_arguments_writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) :
    WritesWithin (saveArgumentsEffect s).components #v[ScalarFrame.workRegion initial 9992] := by
  intro c hc a ha
  simp only [saveArgumentsEffect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 464) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 464)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 712) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 456) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 456)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 720) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 384) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 384)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 792) (by decide) (by decide) ha⟩

theorem save_arguments_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (ready : ReadyToStep t)
    (effect : (saveArgumentsEffect s).Holds s t) : Frame initial t := by
  apply state.after_effect pre (by decide) ready effect.agrees _
    (by simp [saveArgumentsEffect, Effect.components, Write.component, Operand.component])
    (by simp [saveArgumentsEffect, Effect.components, Write.component, Operand.component])
    (by simp [saveArgumentsEffect, Effect.components, Write.component, Operand.component])
    (by simp [saveArgumentsEffect, Effect.components, Write.component, Operand.component])
  intro c hc a ha
  obtain ⟨region, member, inside⟩ := save_arguments_writes pre state c hc a ha
  exact ⟨region, by simpa using Or.inr member, inside⟩

theorem arguments_saved [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992) :
    ∃ t, ArgumentsSaved initial t boundary := by
  obtain ⟨s, runS, state, ripS, agreesS⟩ := entry_frame pre
  obtain ⟨fuel, t, runT, readyT, _, effect⟩ := save_arguments_correct boundary
    pre.outerBoundary s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd581 saveArgumentsBytes
      (by decide) (by decide +kernel)) (save_arguments_pre pre state ripS)
  have frameT := save_arguments_frame pre state readyT effect
  have regs (r : BitVec 5) (notRsp : r ≠ 4) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read initial := by
    apply (effect.agrees.read (by
      simp [saveArgumentsEffect, Effect.components, Write.component, Operand.component])).trans
    exact agreesS.read (by simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq]; simp; exact notRsp)
  have writes := effect.writes
  simp only [saveArgumentsEffect, Write.AllHold, Operand.read] at writes
  refine ⟨t, {
    toFrameState := frameT
    stackFrame := memoryWriteFrame_trans
      (ScalarFrame.save_frame pre (by decide) agreesS (by simp [Component.Covers]))
      (work_frame_stack pre (effect.agrees.memoryWriteFrame (save_arguments_writes pre state)))
    execution := ⟨7 + fuel, runS.trans runT⟩
    rip := effect.rip
    keyPointer := regs 6 (by decide)
    outputPointer := regs 7 (by decide)
    descriptors := regs 2 (by decide)
    count := regs 1 (by decide)
    signaturePointer := regs 8 (by decide)
    savedKey := ?_
    savedOutput := ?_
    savedSignature := ?_
  }⟩
  · change memLoad t.external (stackPtr initial - 1176 + 456) 64 = _
    rw [← state.rsp, writes.2.1]
    exact agreesS.read (n := 64) (r := 6) (by simp [saveFrame])
  · change memLoad t.external (stackPtr initial - 1176 + 384) 64 = _
    rw [← state.rsp, writes.2.2]
    exact agreesS.read (n := 64) (r := 7) (by simp [saveFrame])
  · change memLoad t.external (stackPtr initial - 1176 + 464) 64 = _
    rw [← state.rsp, writes.1]
    exact agreesS.read (n := 64) (r := 8) (by simp [saveFrame])

end P256.Proofs.Verifying.Message
