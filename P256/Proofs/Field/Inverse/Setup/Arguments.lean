import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field

structure ParameterMiddlePre (s : RamState) : Prop where
  rip : s.RIP = 0x1140cc
  writable : MemWritable s ((Operand.reg 4 : Operand 64).read s + 104) 8
  apart : RangeApart ((Operand.reg 4 : Operand 64).read s + 104) 8 0x1140cc 14

def parameterMiddleBytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x68,0xff,0xff,0xff,0xff,0x4c,0x8d,0x44,0x24,0x48]

def parameterMiddleEffect (s : RamState) : Effect :=
  { rip := 0x1140da
    writes := [
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64), 0xffffffffffffffff⟩,
      ⟨(.reg 8 : Operand 64), (Operand.reg 4 : Operand 64).read s + 72⟩] }

theorem parameter_middle_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1140cc parameterMiddleBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x140cc parameterMiddleBytes
    (by decide) (by decide +kernel)

theorem parameter_middle [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ParameterMiddlePre (codeRange 0x1140cc parameterMiddleBytes)
      (Effect.post parameterMiddleEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x1140cc 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl 0xffffffff)
  case pre => intro s h; exact ⟨h.rip, h.writable, h.apart.sub 0 9 (by decide)⟩
  case av =>
    intro s h
    exact Effect.avoids_of_components_mem_rip (by x86_norm [Effect.components]) h.apart
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x140d5 (by decide))
  advance_then (lea_r64_effect_step 0x1140d5 0x4c (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1140cc parameterMiddleBytes 9 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),
      Effect.Avoids.of_noMem (by simp [leaR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x140da (by decide))⟩
  advance_finish [parameterMiddleEffect]

def parameterArgumentBytes : List UInt8 :=
  [0x48,0x89,0xe7,0x48,0x8d,0x54,0x24,0x28,0x48,0xc7,0xc1,0xff,0xff,0xff,0xff]

def parameterArgumentEffect (s : RamState) : Effect :=
  { rip := 0x114119
    writes := [
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩,
      ⟨(.reg 1 : Operand 64), 0xffffffffffffffff⟩] }

theorem parameter_arguments_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11410a parameterArgumentBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1410a parameterArgumentBytes
    (by decide) (by decide +kernel)

theorem parameter_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x11410a)
      (codeRange 0x11410a parameterArgumentBytes) (Effect.post parameterArgumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x11410a 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1410d (by decide))
  advance_then (lea_r64_effect_step 0x11410d 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11410a parameterArgumentBytes 3 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),
      Effect.Avoids.of_noMem (by simp [leaR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x14112 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x114112 0x48 0xc1 (by simp [RexWPrefix])
    rfl rfl 0xffffffff)
  case sub => exact codeRange_slice_subset 0x11410a parameterArgumentBytes 8 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),
      Effect.Avoids.of_noMem (by simp [movR64Imm32Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x14119 (by decide))⟩
  advance_finish [parameterArgumentEffect]

end P256.Proofs.Field.Inverse
