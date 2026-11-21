import P256.Proofs.Verifying.Message.Convert.Context
import P256.Proofs.Verifying.Message.Convert.Registers

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Head [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10d964
  source : s.regValue .rdx = initial.regValue .rsi
  yPointer : s.regValue .rbx = frameBase initial + 32

theorem head [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Pre initial boundary message)
    (state : Hash.Result initial s boundary message) :
    ∃ t, Head initial t boundary message := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := head_setup boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd957 headBytes
      (by decide) (by decide +kernel))
    ⟨state.rip, stack_readable (frameOffset := 1176) pre.toCalleePre state.toFrameState
      (by decide) (by decide)⟩
  have context := (Context.of_hash state).after_registers run ready effect.agrees
    (by simp [headEffect, Effect.components, Component.Covers])
    (by simp [headEffect, Effect.components]) (by simp [headEffect, Effect.components])
    (by simp [headEffect, Effect.components]) (by simp [headEffect, Effect.components])
  have stack : stackPtr s = frameBase initial := state.rsp
  refine ⟨t, context, effect.rip, ?_, ?_⟩
  · have value : t.regValue .rdx = memLoad s.external (stackPtr s + 456) 64 := effect.writes.2
    rw [value, stack]
    exact state.savedKey
  · have value : t.regValue .rbx = stackPtr s + 32 := effect.writes.1
    rw [value, stack]

end P256.Proofs.Verifying.Message.Convert
