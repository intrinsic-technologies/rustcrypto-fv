import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.Verifying.Message.Arguments
import P256.Proofs.Verifying.Message.ConstantsState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem constants_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (rip : s.RIP = 0x10d599) : ConstantsPre s := by
  refine ⟨rip, ?_, ?_⟩
  · intro offset len bound positive
    exact ScalarFrame.stack_writable (frameOffset := 1176) pre state (by decide)
      (by omega) positive
  · intro offset len bound codeOffset codeLen codeBound
    exact ScalarFrame.stack_code (frameOffset := 1176) pre state (by decide)
      (by omega) codeBound

theorem constants_writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) :
    WritesWithin (constantsEffect s).components #v[ScalarFrame.workRegion initial 9992] := by
  intro c hc a ha
  simp only [constantsEffect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 560) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 560)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 616) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 552) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 552)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 624) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 544) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 544)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 632) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 536) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 536)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 640) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 568) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 568)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 608) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 535) 1).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 535)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨ScalarFrame.workRegion initial 9992, by simp,
      ScalarFrame.work_contains pre (offset := 641) (by decide) (by decide) ha⟩

theorem constants_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (ready : ReadyToStep t)
    (effect : (constantsEffect s).Holds s t) : Frame initial t := by
  apply state.after_effect pre (by decide) ready effect.agrees _
    (by simp [constantsEffect, Effect.components, Write.component, Operand.component])
    (by simp [constantsEffect, Effect.components, Write.component, Operand.component])
    (by simp [constantsEffect, Effect.components, Write.component, Operand.component])
    (by simp [constantsEffect, Effect.components, Write.component, Operand.component])
  intro c hc a ha
  obtain ⟨region, member, inside⟩ := constants_writes pre state c hc a ha
  exact ⟨region, by simpa using Or.inr member, inside⟩

structure Initialized [Bindings] (initial t : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame initial t where
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]
  execution : ∃ fuel, Advances boundary fuel initial t
  rip : t.RIP = 0x10d5f5
  hash : HMAC.Sha256StateAt t (frameBase initial + 472) .empty
  arguments : ∃ s, ArgumentsSaved initial s boundary ∧ (constantsEffect s).Holds s t

theorem initialize_correct [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992) :
    ∃ t, Initialized initial t boundary := by
  obtain ⟨s, saved⟩ := arguments_saved pre
  have cp := constants_pre pre saved.toFrameState saved.rip
  obtain ⟨fuel, t, run, ready, _, effect⟩ := constants_run boundary pre.outerBoundary s
    (readyToStep saved.machine saved.bindingsSupported)
    (programText_slice (programLoaded_codeIn saved.loaded) 0xd599 constantsBytes
      (by decide) (by decide +kernel)) cp
  refine ⟨t, {
    toFrameState := constants_frame pre saved.toFrameState ready effect
    stackFrame := memoryWriteFrame_trans saved.stackFrame
      (work_frame_stack pre
        (effect.agrees.memoryWriteFrame (constants_writes pre saved.toFrameState)))
    execution := ?_
    rip := effect.rip
    hash := ?_
    arguments := ⟨s, saved, effect⟩
  }⟩
  · obtain ⟨before, runBefore⟩ := saved.execution
    exact ⟨before + fuel, runBefore.trans run⟩
  · have hash := constants_state cp effect
    change HMAC.Sha256StateAt t (stackPtr initial - 1176 + 472) .empty
    rw [← saved.rsp]
    exact hash

end P256.Proofs.Verifying.Message
