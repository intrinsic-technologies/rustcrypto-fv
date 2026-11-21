import P256.Proofs.Signing.Wrapper.Hash.Frame
import P256.Proofs.Signing.Wrapper.Hash.ConstantsState

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem constants_pre [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : Context initial secret message) (state : Frame initial start s)
    (rip : s.RIP = 0x102720) : ConstantsPre s := by
  refine ⟨rip, ?_, ?_⟩
  · intro offset len bound positive
    exact stack_writable pre state (by omega) positive
  · intro offset len bound codeOffset codeLen codeBound
    exact stack_code pre state (by omega) codeBound

theorem constants_writes [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : Context initial secret message) (state : Frame initial start s) :
    WritesWithin (constantsEffect s).components #v[workRegion initial] := by
  intro c hc a ha
  simp only [constantsEffect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 264) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 264)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 256) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 256) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 256)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 264) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 248) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 248)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 272) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 240) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 240)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 280) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 272) 8).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 272)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 248) (by decide) (by decide) ha⟩
  · change (Component.mem (stackPtr s + BitVec.ofNat 64 239) 1).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 239)
      state.rsp (by decide) (by decide)] at ha
    exact ⟨workRegion initial, by simp,
      work_contains pre (offset := 281) (by decide) (by decide) ha⟩


structure Initialized [Bindings] (initial start t : RamState) (message : ByteArray) : Prop
    extends Frame initial start t where
  rip : t.RIP = 0x10277c
  hash : HMAC.Sha256StateAt t (frameBase initial + 176) .empty
  pointer : t.regValue .rsi = start.regValue .rsi
  length : t.regValue .rbp = BitVec.ofNat 64 message.size

theorem initialize_correct [Bindings] {initial start : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) :
    ∃ t, Initialized initial start t message := by
  have state := initial_frame pre
  have cp := constants_pre pre.context state pre.rip
  obtain ⟨fuel, t, run, ready, _, effect⟩ := constants_run (returnBoundary initial)
    (outside pre.context) start (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2720 constantsBytes
      (by decide) (by decide +kernel)) cp
  refine ⟨t, {
    toFrame := state.after_effect pre.context run ready effect.agrees
      (constants_writes pre.context state) ?_ ?_
    rip := effect.rip
    hash := ?_
    pointer := effect.agrees.read (n := 64) (r := 6) (by
      simp [constantsEffect, Effect.components, Write.component, Operand.component])
    length := (effect.agrees.read (n := 64) (r := 5) (by
      simp [constantsEffect, Effect.components, Write.component, Operand.component])).trans pre.length
  }⟩
  · exact (effect.agrees.read (n := 64) (r := 4) (by
      simp [constantsEffect, Effect.components, Write.component, Operand.component])).trans state.rsp
  · simp [constantsEffect, Effect.components, Write.component, Operand.component]
  · have hash := constants_state cp effect
    change HMAC.Sha256StateAt t (stackPtr initial - 520#64 + 176#64) .empty
    rw [← state.rsp]
    exact hash

end P256.Proofs.Signing.Wrapper.Hash
