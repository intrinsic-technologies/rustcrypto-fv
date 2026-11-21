import P256.Proofs.Verifying.Core.Registers

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Initialized [Bindings] (s t : RamState) : Prop extends Frame s t where
  rip : t.RIP = 0x10da55
  signature : t.regValue .rbx = s.regValue .r8

def initializeClobbers : List Component := [.reg 3, .rip]

theorem initialize_full [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10da4d)
    (signature : memLoad t.external (frameBase s + 464) 64 = s.regValue .r8) :
    ∃ fuel u, Advances boundary fuel t u ∧ Initialized s u ∧
      u.external = t.external ∧ AgreesExcept initializeClobbers t u := by
  obtain ⟨n, u, run, ready, _, effect⟩ :=
    registers_correct boundary pre.outerBoundary t
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xda4d registerBytes
        (by decide) (by decide +kernel))
      ⟨rip, ScalarFrame.stack_readable (frameOffset := 1176) pre.toCalleePre frame
        (by decide) (by decide)⟩
  have agrees : AgreesExcept initializeClobbers t u := by
    simpa [registerEffect, Effect.components, Write.component, Operand.component,
      initializeClobbers] using effect.agrees
  have state := frame.after_registers ready agrees
    (by simp [initializeClobbers, Component.Covers]) (by simp [initializeClobbers])
  have value : u.regValue .rbx = memLoad t.external (stackPtr t + 464) 64 := effect.writes
  refine ⟨n, u, run, ⟨state, effect.rip, ?_⟩,
    agrees.external (by simp [initializeClobbers, Component.Covers]), agrees⟩
  rw [frame.rsp] at value
  exact value.trans signature

theorem initialize_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10da4d)
    (signature : memLoad t.external (frameBase s + 464) 64 = s.regValue .r8) :
    ∃ fuel u, Advances boundary fuel t u ∧ Initialized s u ∧ u.external = t.external := by
  obtain ⟨n, u, run, state, memory, _⟩ := initialize_full pre frame rip signature
  exact ⟨n, u, run, state, memory⟩

end P256.Proofs.Verifying.Core
