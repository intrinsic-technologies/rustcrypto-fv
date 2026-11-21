import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure HeadPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d957
  read232 : MemReadable s (stackPtr s + 456) 8

def headBytes : List UInt8 := [0x48, 0x8d, 0x5c, 0x24, 0x20, 0x48, 0x8b, 0x94, 0x24, 0xc8, 0x1, 0x0, 0x0]

def headEffect (s : RamState) : Effect :=
  { rip := 0x10d964
    writes := [⟨(.reg 3 : Operand 64), stackPtr s + 32⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (stackPtr s + 456) 64⟩] }

theorem head_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary HeadPre (codeRange 0x10d957 headBytes)
      (Effect.post headEffect) := by
  advance_begin (lea_r64_effect_step 0x10d957 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case next => intro s hp; exact boundary_ne_program outside (inProgram_of_textOffset 0xd95c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d95c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d957 headBytes 5 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd964 (by decide))⟩
    x86_norm
    exact hp.read232
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [headEffect]
  · x86_norm [headEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [headEffect]
  · x86_norm [headEffect]

structure IdentityPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d9df

def identityBytes : List UInt8 := [0x4c, 0x8d, 0xbc, 0x24, 0x80, 0x0, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x48, 0xc7, 0xc6, 0x90, 0x24, 0x20, 0x0]

def identityEffect (s : RamState) : Effect :=
  { rip := 0x10d9f6
    writes := [⟨(.reg 15 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 1 : Operand 64), 12⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 6 : Operand 64), 0x202490⟩] }

theorem identity_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary IdentityPre (codeRange 0x10d9df identityBytes)
      (Effect.post identityEffect) := by
  advance_begin (lea_r64_effect_step 0x10d9df 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case next => intro s hp; exact boundary_ne_program outside (inProgram_of_textOffset 0xd9e7 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10d9e7 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10d9df identityBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd9ec (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d9ec 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d9df identityBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd9ef (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10d9ef 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202490)
  case sub => exact codeRange_slice_subset 0x10d9df identityBytes 16 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd9f6 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [identityEffect]
  · x86_norm [identityEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [identityEffect]
  · x86_norm [identityEffect]


end P256.Proofs.Verifying.Message.Convert
