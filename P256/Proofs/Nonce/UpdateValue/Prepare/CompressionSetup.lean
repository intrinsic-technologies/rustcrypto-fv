import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
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

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.CompressionSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

attribute [local x86_compose] movM8Imm8Effect

@[local x86_local] theorem byteStore_local (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8Effect p am imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a9ae
  writable : ∀ slot ∈ ([(168,8),(176,8),(184,8),(192,8),(200,8),(167,1)] : List (Nat × Nat)),
    MemWritable s (rspOf s + BitVec.ofNat 64 slot.1) slot.2
  codeApart : ∀ slot ∈ ([(168,8),(176,8),(184,8),(192,8),(200,8),(167,1)] : List (Nat × Nat)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 slot.1) slot.2
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0xb8, 0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0xb8, 0x7f, 0x52, 0xe, 0x51, 0x8c, 0x68, 0x5, 0x9b, 0x48, 0x89, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0xb8, 0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0xb8, 0x67, 0xe6, 0x9, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0xa7, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x8, 0xba, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf7]

def effect (s : RamState) : Effect :=
  { rip := 0x10aa1f
    writes := [
      ⟨(.reg 14 : Operand 64), rspOf s + 168⟩,
      ⟨(.reg 0 : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (rspOf s + 192) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (rspOf s + 184) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (rspOf s + 176) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (rspOf s + 168) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (rspOf s + 167) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s + 200) : Operand 64), 1⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 8⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 168⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a9ae bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa9ae bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a9ae bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a9ae 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa9b6 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a9b6 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 8 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9c0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a9c0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (192,8) (by simp)
    · x86_norm
      exact hP.codeApart (192,8) (by simp) 0xa9c0 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (192,8) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9c8 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a9c8 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 26 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9d2 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a9d2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (184,8) (by simp)
    · x86_norm
      exact hP.codeApart (184,8) (by simp) 0xa9d2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (184,8) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9da (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a9da 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 44 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9e4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a9e4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 54 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (176,8) (by simp)
    · x86_norm
      exact hP.codeApart (176,8) (by simp) 0xa9e4 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (176,8) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9ec (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a9ec 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 62 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9f6 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a9f6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (168,8) (by simp)
    · x86_norm
      exact hP.codeApart (168,8) (by simp) 0xa9f6 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (168,8) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9fe (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10a9fe (.sib 4 none 0 (.d32 167)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (167,1) (by simp)
    · x86_norm
      exact hP.codeApart (167,1) (by simp) 0xa9fe 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (167,1) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa06 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10aa06 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 88 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (200,8) (by simp)
    · x86_norm
      exact hP.codeApart (200,8) (by simp) 0xaa06 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (200,8) (by simp) 0xa9ae 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa12 (by decide))
  advance_then (lea_r64_effect_step 0x10aa12 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 100 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa17 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10aa17 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 105 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa1c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10aa1c 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a9ae bytes 110 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa1f (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.UpdateValue.Prepare.CompressionSetup
