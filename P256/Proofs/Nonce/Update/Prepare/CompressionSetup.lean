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

namespace P256.Proofs.Nonce.Update.Prepare.CompressionSetup

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
  rip : s.RIP = 0x109fee
  writable : ∀ slot ∈ ([(320, 8),(328, 8),(336, 8),(344, 8),(352, 8),(319, 1)] : List (Nat × Nat)),
    MemWritable s (rspOf s + BitVec.ofNat 64 slot.1) slot.2
  codeApart : ∀ slot ∈ ([(320, 8),(328, 8),(336, 8),(344, 8),(352, 8),(319, 1)] : List (Nat × Nat)),
    ∀ offset len : Nat, offset + len ≤ 83119 →
    RangeApart (rspOf s + BitVec.ofNat 64 slot.1) slot.2
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0xb8, 0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0x58, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x7f, 0x52, 0xe, 0x51, 0x8c, 0x68, 0x5, 0x9b, 0x48, 0x89, 0x84, 0x24, 0x50, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x67, 0xe6, 0x9, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x3f, 0x1, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x60, 0x1, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x58, 0xba, 0x1, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a05c
    writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 320⟩,
      ⟨(.reg 0 : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (rspOf s + 344) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (rspOf s + 336) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (rspOf s + 320) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (rspOf s + 319) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s + 352) : Operand 64), 1⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 88⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x109fee bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x9fee bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x109fee bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x109fee 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x9ff6 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x109ff6 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case sub => exact codeRange_slice_subset 0x109fee bytes 8 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa000 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a000 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109fee bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (344, 8) (by simp)
    · x86_norm
      exact hP.codeApart (344, 8) (by simp) 0xa000 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (344, 8) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa008 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a008 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x109fee bytes 26 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa012 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a012 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109fee bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (336, 8) (by simp)
    · x86_norm
      exact hP.codeApart (336, 8) (by simp) 0xa012 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (336, 8) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa01a (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a01a 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x109fee bytes 44 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa024 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a024 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109fee bytes 54 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (328, 8) (by simp)
    · x86_norm
      exact hP.codeApart (328, 8) (by simp) 0xa024 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (328, 8) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa02c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a02c 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x109fee bytes 62 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa036 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a036 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109fee bytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (320, 8) (by simp)
    · x86_norm
      exact hP.codeApart (320, 8) (by simp) 0xa036 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (320, 8) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa03e (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10a03e (.sib 4 none 0 (.d32 319)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109fee bytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (319, 1) (by simp)
    · x86_norm
      exact hP.codeApart (319, 1) (by simp) 0xa03e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (319, 1) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa046 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a046 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x109fee bytes 88 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (352, 8) (by simp)
    · x86_norm
      exact hP.codeApart (352, 8) (by simp) 0xa046 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (352, 8) (by simp) 0x9fee 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa052 (by decide))
  advance_then (lea_r64_effect_step 0x10a052 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109fee bytes 100 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa057 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a057 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x109fee bytes 105 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa05c (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Prepare.CompressionSetup
