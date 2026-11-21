import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

attribute [local x86_compose] memLoad_after memLoad_memStore_constants

structure ArenaPre (s : RamState) : Prop where
  rip : s.RIP = 0x103020
  heapLength : MemReadable s (stackPtr s + 288) 8
  writable : ∀ off ∈ ([0,8,16,24,32] : List Nat),
    Writable s (0x300000 + BitVec.ofNat 64 off) 8

def arenaBytes : List UInt8 :=
  [72, 139, 132, 36, 32, 1, 0, 0, 76, 137, 13, 209, 207, 31, 0, 72, 137, 5, 210, 207, 31, 0, 72, 199, 5, 207, 207, 31, 0, 0, 0, 0, 0, 72, 199, 5, 204, 207, 31, 0, 1, 0, 0, 0, 72, 199, 5, 201, 207, 31, 0, 0, 0, 0, 0]

def arenaEffect (s : RamState) : Effect :=
  { rip := 0x103057
    writes := [⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 288) : Operand 64).read s⟩,
      ⟨(.mem 0x300000 : Operand 64), s.regValue .r9⟩,
      ⟨(.mem 0x300008 : Operand 64), (Operand.mem (stackPtr s + 288) : Operand 64).read s⟩,
      ⟨(.mem 0x300010 : Operand 64), 0⟩,
      ⟨(.mem 0x300018 : Operand 64), 1⟩,
      ⟨(.mem 0x300020 : Operand 64), 0⟩] }

theorem arena_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArenaPre (codeRange 0x103020 arenaBytes)
      (Effect.post arenaEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x103020 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.heapLength⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x3028 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x103028 0x4c (by simp [RexWPrefix]) 1
    (.rip 0x1fcfd1) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103020 arenaBytes 8 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact static_code_apart 0 0x3028 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 0 0x3020 55 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x302f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10302f 0x48 (by simp [RexWPrefix]) 0
    (.rip 0x1fcfd2) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103020 arenaBytes 15 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact static_code_apart 8 0x302f 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 8 0x3020 55 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3036 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x103036 0x48 (by simp [RexWPrefix])
    (.rip 0x1fcfcf) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x103020 arenaBytes 22 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact static_code_apart 16 0x3036 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 16 0x3020 55 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3041 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x103041 0x48 (by simp [RexWPrefix])
    (.rip 0x1fcfcc) (by decide +kernel) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x103020 arenaBytes 33 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact static_code_apart 24 0x3041 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 24 0x3020 55 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x304c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10304c 0x48 (by simp [RexWPrefix])
    (.rip 0x1fcfc9) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x103020 arenaBytes 44 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact static_code_apart 32 0x304c 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 32 0x3020 55 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3057 (by decide))
  advance_finish [arenaEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, UInt8.toBitVec_ofNat,
    BitVec.reduceExtractLsb', BitVec.reduceToNat]

end P256.Proofs.Verifying.Wrapper
