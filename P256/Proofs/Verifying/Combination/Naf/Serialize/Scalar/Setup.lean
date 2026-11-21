import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
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
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def fillSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x74, 0x24, 0x10, 0xba, 0x1, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x31, 0xf6]

def fillSetupEffect (s : RamState) : Effect :=
  { rip := 0x10b31a
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 16⟩,
      ⟨(Operand.reg 2 : Operand 64), 257⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 16⟩,
      ⟨(Operand.reg 6 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem fillSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b30b)
      (codeRange 0x10b30b fillSetupBytes) (Effect.post fillSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b30b 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb310 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b310 0xba (by decide) 257)
  case sub => exact codeRange_slice_subset 0x10b30b fillSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb315 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b315 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b30b fillSetupBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb318 (by decide))⟩
  advance_then (xor_r32_r32_effect_step 0x10b318 0xf6 rfl)
  case sub => exact codeRange_slice_subset 0x10b30b fillSetupBytes 13 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb31a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [fillSetupEffect, show modrmRm 246 = 6 from rfl, show modrmReg 246 = 6 from rfl, BitVec.xor_self, BitVec.setWidth_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [fillSetupEffect, show modrmRm 246 = 6 from rfl, show modrmReg 246 = 6 from rfl, BitVec.xor_self, BitVec.setWidth_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [fillSetupEffect, show modrmRm 246 = 6 from rfl, show modrmReg 246 = 6 from rfl, BitVec.xor_self, BitVec.setWidth_zero]
  · x86_norm [fillSetupEffect, show modrmRm 246 = 6 from rfl, show modrmReg 246 = 6 from rfl, BitVec.xor_self, BitVec.setWidth_zero]
    all_goals (repeat first | constructor | rfl)

def recodeSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x94, 0x24, 0x38, 0x1, 0x0, 0x0, 0xbe, 0x1, 0x1, 0x0, 0x0, 0xb9, 0x20, 0x0, 0x0, 0x0, 0x41, 0xb8, 0x0, 0x1, 0x0, 0x0, 0x41, 0xb9, 0x5, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf7]

def recodeSetupEffect (s : RamState) : Effect :=
  { rip := 0x10b341
    writes := [⟨(Operand.reg 2 : Operand 64), stackPtr s + 312⟩,
      ⟨(Operand.reg 6 : Operand 64), 257⟩,
      ⟨(Operand.reg 1 : Operand 64), 32⟩,
      ⟨(Operand.reg 8 : Operand 64), 256⟩,
      ⟨(Operand.reg 9 : Operand 64), 5⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩] }

theorem recodeSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b320)
      (codeRange 0x10b320 recodeSetupBytes) (Effect.post recodeSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b320 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb328 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b328 0xbe (by decide) 257)
  case sub => exact codeRange_slice_subset 0x10b320 recodeSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb32d (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10b32d 0xb9 (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10b320 recodeSetupBytes 13 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb332 (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10b332 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 256)
  case sub => exact codeRange_slice_subset 0x10b320 recodeSetupBytes 18 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb338 (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10b338 0x41 0xb9 (by simp [RexNoWPrefix]) (by decide) 5)
  case sub => exact codeRange_slice_subset 0x10b320 recodeSetupBytes 24 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb33e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b33e 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b320 recodeSetupBytes 30 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb341 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [recodeSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [recodeSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [recodeSetupEffect]
  · x86_norm [recodeSetupEffect]
    all_goals (repeat first | constructor | rfl)

def outputSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x74, 0x24, 0x8, 0xba, 0x10, 0x1, 0x0, 0x0, 0x48, 0x89, 0xdf]

def outputSetupEffect (s : RamState) : Effect :=
  { rip := 0x10b358
    writes := [⟨(Operand.reg 6 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .rbx⟩] }

theorem outputSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b34b)
      (codeRange 0x10b34b outputSetupBytes) (Effect.post outputSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b34b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb350 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b350 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x10b34b outputSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb355 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b355 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b34b outputSetupBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb358 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [outputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [outputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [outputSetupEffect]
  · x86_norm [outputSetupEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
