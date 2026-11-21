import P256.Proofs.SignatureFromSlice.Wrapper.Save
import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

attribute [local x86_compose] memLoad_after memLoad_memStore_constants

structure ArenaPre (s : RamState) : Prop where
  rip : s.RIP = 0x102227
  heapLength : MemReadable s (stackPtr s + 96) 8
  writable : ∀ off ∈ ([0,8,16,24,32] : List Nat),
    Writable s (0x300000 + BitVec.ofNat 64 off) 8

def arenaBytes : List UInt8 :=
  [72, 139, 68, 36, 96, 76, 137, 13, 205, 221, 31, 0, 72, 137, 5, 206, 221, 31, 0, 72, 199, 5, 203, 221, 31, 0, 0, 0, 0, 0, 72, 199, 5, 200, 221, 31, 0, 1, 0, 0, 0, 72, 199, 5, 197, 221, 31, 0, 0, 0, 0, 0]

def arenaEffect (s : RamState) : Effect :=
  { rip := 0x10225b
    writes := [⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 96) : Operand 64).read s⟩,
      ⟨(.mem 0x300000 : Operand 64), s.regValue .r9⟩,
      ⟨(.mem 0x300008 : Operand 64), (Operand.mem (stackPtr s + 96) : Operand 64).read s⟩,
      ⟨(.mem 0x300010 : Operand 64), 0⟩,
      ⟨(.mem 0x300018 : Operand 64), 1⟩,
      ⟨(.mem 0x300020 : Operand 64), 0⟩] }

theorem arena_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArenaPre (codeRange 0x102227 arenaBytes)
      (Effect.post arenaEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x102227 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.heapLength⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x222c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10222c 0x4c (by simp [RexWPrefix]) 1
    (.rip 0x1fddcd) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102227 arenaBytes 5 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact static_code_apart 0 0x222c 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 0 0x2227 52 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2233 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x102233 0x48 (by simp [RexWPrefix]) 0
    (.rip 0x1fddce) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102227 arenaBytes 12 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact static_code_apart 8 0x2233 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 8 0x2227 52 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x223a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10223a 0x48 (by simp [RexWPrefix])
    (.rip 0x1fddcb) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102227 arenaBytes 19 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact static_code_apart 16 0x223a 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 16 0x2227 52 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2245 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x102245 0x48 (by simp [RexWPrefix])
    (.rip 0x1fddc8) (by decide +kernel) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x102227 arenaBytes 30 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact static_code_apart 24 0x2245 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 24 0x2227 52 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2250 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x102250 0x48 (by simp [RexWPrefix])
    (.rip 0x1fddc5) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102227 arenaBytes 41 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact static_code_apart 32 0x2250 11 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact static_code_apart 32 0x2227 52 (by decide) (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x225b (by decide))
  advance_finish [arenaEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, UInt8.toBitVec_ofNat,
    BitVec.reduceExtractLsb', BitVec.reduceToNat]

end P256.Proofs.SignatureFromSlice.Wrapper
