import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copySetupBytes : List UInt8 :=
  [0x48,0x8d,0x94,0x24,0x8,0x1,0x0,0x0,0xb9,0x9,0x0,0x0,0x0,0x48,0x89,0xd7,0x4c,0x89,0xfe]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x10ea94
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 264⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 264⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem copy_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ea81)
      (codeRange 0x10ea81 copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10ea81 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xea89 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10ea89 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x10ea81 copySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xea8e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ea8e 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ea81 copySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xea91 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ea91 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ea81 copySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xea94 (by decide))⟩
  advance_finish [copySetupEffect]

structure ConstantSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ea97
  writable : MemWritable s ((Operand.reg 4 : Operand 64).read s + 336) 1
  apart : ∀ off len : Nat, off + len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + 336) 1
      (Extracted.textAddress + BitVec.ofNat 64 off) len

def constantSetupBytes : List UInt8 :=
  [0x40,0x88,0xac,0x24,0x50,0x1,0x0,0x0,0x48,0x8d,0x84,0x24,0x8,0x4,0x0,0x0,0xb9,0x9,0x0,0x0,0x0,0x48,0x89,0xc7,0x48,0xc7,0xc6,0xf0,0x24,0x20,0x0]

def constantSetupEffect (s : RamState) : Effect :=
  { rip := 0x10eab6
    writes := [⟨(.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 8),
        (Operand.reg 5 : Operand 8).read s⟩,
      ⟨(.reg 0 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1032⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1032⟩,
      ⟨(.reg 6 : Operand 64), 0x2024f0⟩] }

theorem constant_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ConstantSetupPre (codeRange 0x10ea97 constantSetupBytes)
      (Effect.post constantSetupEffect) := by
  advance_begin (mov_m8_r8_effect_step 0x10ea97 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.writable, hP.apart 0xea97 8 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 0xea97 31 (by decide)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xea9f (by decide))
  advance_then (lea_r64_effect_step 0x10ea9f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 1032)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea97 constantSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeaa7 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10eaa7 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x10ea97 constantSetupBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeaac (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10eaac 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ea97 constantSetupBytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeaaf (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10eaaf 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x2024f0)
  case sub => exact codeRange_slice_subset 0x10ea97 constantSetupBytes 24 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeab6 (by decide))⟩
  advance_finish [constantSetupEffect]

end P256.Proofs.PublicPoint.Normalize.Finish
