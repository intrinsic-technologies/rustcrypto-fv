import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copySetupBytes : List UInt8 :=
  [0x48,0x8d,0x94,0x24,0xf8,0x3,0x0,0x0,0xb9,0x9,0x0,0x0,0x0,0x48,0x89,0xd7,0x4c,0x89,0xfe]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x100496
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1016⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1016⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem copy_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100483)
      (codeRange 0x100483 copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x100483 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 1016)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x48b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10048b 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x100483 copySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x490 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100490 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100483 copySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x493 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100493 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100483 copySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x496 (by decide))⟩
  advance_finish [copySetupEffect]

structure ConstantSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x100499
  writable : MemWritable s ((Operand.reg 4 : Operand 64).read s + 1088) 1
  apart : ∀ off len : Nat, off + len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + 1088) 1
      (Extracted.textAddress + BitVec.ofNat 64 off) len

def constantSetupBytes : List UInt8 :=
  [0x40, 0x88, 0xac, 0x24, 0x40, 0x4, 0x0, 0x0, 0x48, 0x8d, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0xb9, 0x9, 0x0, 0x0, 0x0, 0x48, 0x89, 0xc7, 0x48, 0xc7, 0xc6, 0xf0, 0x24, 0x20, 0x0]

def constantSetupEffect (s : RamState) : Effect :=
  { rip := 0x1004b8
    writes := [⟨(.mem ((Operand.reg 4 : Operand 64).read s + 1088) : Operand 8),
        (Operand.reg 5 : Operand 8).read s⟩,
      ⟨(.reg 0 : Operand 64), (Operand.reg 4 : Operand 64).read s + 248⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 248⟩,
      ⟨(.reg 6 : Operand 64), 0x2024f0⟩] }

theorem constant_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ConstantSetupPre (codeRange 0x100499 constantSetupBytes)
      (Effect.post constantSetupEffect) := by
  advance_begin (mov_m8_r8_effect_step 0x100499 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d32 1088)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.writable, hP.apart 0x499 8 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 0x499 31 (by decide)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x4a1 (by decide))
  advance_then (lea_r64_effect_step 0x1004a1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100499 constantSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4a9 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x1004a9 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x100499 constantSetupBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4ae (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1004ae 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100499 constantSetupBytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4b1 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x1004b1 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x2024f0)
  case sub => exact codeRange_slice_subset 0x100499 constantSetupBytes 24 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4b8 (by decide))⟩
  advance_finish [constantSetupEffect]

end P256.Proofs.Ecdh.Normalize.Finish
