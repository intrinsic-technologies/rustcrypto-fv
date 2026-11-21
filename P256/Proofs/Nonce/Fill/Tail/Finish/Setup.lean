import P256.Proofs.Nonce.Fill.Tail.State
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x1076e5
  readable : MemReadable s (stackPtr s + 40) 8

def setupBytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x48,0x4c,0x89,0xfe,0x48,0x8b,0x54,0x24,0x28,0x4c,0x89,0xe9]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x1076f5
    writes := [
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (stackPtr s + 40) 64⟩,
      ⟨(.reg 1 : Operand 64), s.regValue .r13⟩] }

theorem setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1076e5 setupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x76e5 setupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x1076e5 setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x1076e5 0x48 (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x76ea (by decide))
  advance_then (mov_r64_r64_effect_step 0x1076ea 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1076e5 setupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x76ed (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x1076ed 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1076e5 setupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x76f2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1076f2 0x4c 0xe9 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1076e5 setupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x76f5 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ effect
  apply effect.weaken
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, BitVec.add_zero, State.regValue]
    all_goals exact ⟨rfl, rfl⟩
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, BitVec.add_zero, State.regValue]
    all_goals exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]

structure Prepared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Compared initial s orderAddress state where
  rip : s.RIP = 0x1076f5
  rdi : s.regValue .rdi = frameBase initial + 72
  rsi : s.regValue .rsi = orderAddress
  rdx : s.regValue .rdx = initial.regValue .rsi
  rcx : s.regValue .rcx = 32

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (rip : s.RIP = 0x1076e5) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t orderAddress state := by
  have setup : SetupPre s := ⟨rip, stack_readable pre input.toFrame (offset := 40) (by decide)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := setup_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (setup_code input.loaded) setup
  have frame := input.toContext.after_registers ready effect.agrees
    (by simp [setupEffect, Effect.components, Component.Covers])
    (by simp [setupEffect, Effect.components]) (by simp [setupEffect, Effect.components]) (by simp [setupEffect, Effect.components])
  have values := effect.writes
  change t.regValue .rdi = stackPtr s + 72 ∧ t.regValue .rsi = s.regValue .r15 ∧
    t.regValue .rdx = memLoad s.external (stackPtr s + 40) 64 ∧
    t.regValue .rcx = s.regValue .r13 at values
  rw [input.rsp, input.r15, input.outputSlot, input.r13] at values
  refine ⟨fuel, t, run, ⟨⟨frame, ?_⟩, effect.rip, values.1, values.2.1,
    values.2.2.1, values.2.2.2⟩⟩
  have memory := effect.agrees.external
    (by simp [setupEffect, Effect.components, Component.Covers])
  simpa only [Nat256At, memory] using input.integer

end P256.Proofs.Nonce.Fill.Tail.Finish
