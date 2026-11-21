import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

structure RadixArgsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1002f2
  scalar : MemReadable s (stackPtr s + 8) 8

def radixArgsBytes : List UInt8 :=
  [0x4c,0x8d,0x74,0x24,0x50,0x4c,0x89,0xf7,0x48,0x8b,0x74,0x24,0x08]

def radixArgsEffect (s : RamState) : Effect :=
  { rip := 0x1002ff
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 80⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 80⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.mem (stackPtr s + 8) : Operand 64).read s⟩] }

theorem radixArgs_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary RadixArgsPre
      (codeRange 0x1002f2 radixArgsBytes) (Effect.post radixArgsEffect) := by
  advance_begin (lea_r64_effect_step 0x1002f2 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x2f7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1002f7 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1002f2 radixArgsBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x2fa (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x1002fa 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1002f2 radixArgsBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x2ff (by decide))⟩
    x86_norm
    exact hP.scalar
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [radixArgsEffect]
  · x86_norm [radixArgsEffect]
  · intro i; cases i <;> x86_norm [radixArgsEffect]
  · x86_norm [radixArgsEffect]

theorem radixArgs_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : ScalarFrame.FrameState s t 32 3464 2056) (rip : t.RIP = 0x1002f2) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 32 3464 2056 ∧
      (radixArgsEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := radixArgs_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2f2 radixArgsBytes
      (by decide) (by decide +kernel))
    ⟨rip, ScalarFrame.stack_readable pre state (by decide) (by decide)⟩
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [radixArgsEffect,Effect.components,Component.Covers]
  · simp [radixArgsEffect,Effect.components]

end P256.Proofs.Ecdh.Prepare
