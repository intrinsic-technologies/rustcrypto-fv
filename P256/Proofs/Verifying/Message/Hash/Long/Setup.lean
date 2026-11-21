import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Setup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d6b6
  writable : MemWritable s (stackPtr s + 568) 8
  apart : RangeApart (stackPtr s + 568) 8 0x10d6b6 19

def bytes : List UInt8 :=
  [0x48,0x1,0x94,0x24,0x38,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0x18,0x2,0x0,0x0,0x4c,0x89,0xf6]

def effect (s : RamState) : Effect :=
  { rip := 0x10d6c9
    writes := [⟨(.mem (stackPtr s + 568) : Operand 64),
        memLoad s.external (stackPtr s + 568) 64 + s.regValue .rdx⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 536⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d6b6 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd6b6 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d6b6 bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h := add_m64_r64_effect_step 0x10d6b6 0x48
    (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 568)) (by decide) rfl rfl))
  case pre => intro s h; exact ⟨h.rip, h.writable, h.apart.sub 0 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.Avoids.forgetFlags
    exact Effect.avoids_of_mem (by x86_norm [Effect.components, Component.isMem]) h.apart rfl
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd6be (by decide))
  advance_then (lea_r64_effect_step 0x10d6be 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d6b6 bytes 8 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6c6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d6c6 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d6b6 bytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6c9 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Message.Hash.Long.Setup
