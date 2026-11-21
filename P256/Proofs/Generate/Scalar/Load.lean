import P256.Proofs.Generate.Scalar.Prologue
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x112edd
  readable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8

def loadBytes : List UInt8 :=
  [0x4c,0x8b,0x36,0x4c,0x8b,0x7e,0x08,0x49,0x0f,0xce,0x49,0x0f,0xcf,
   0x4c,0x8b,0x66,0x10,0x49,0x0f,0xcc,0x48,0x89,0xfb,0x4c,0x8b,0x6e,0x18,0x49,0x0f,0xcd]

def loadEffect (s : RamState) : Effect :=
  { rip := 0x112efb
    writes := [
      ⟨(.reg 14 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s) 64)⟩,
      ⟨(.reg 15 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 8) 64)⟩,
      ⟨(.reg 12 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 16) 64)⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 24) 64)⟩] }

theorem load_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x112edd loadBytes) (Effect.post loadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x112edd 0x4c (by simp [RexWPrefix]) 6 (.base 6 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s ((Operand.reg 6 : Operand 64).read s + 0) 8
    exact hP.readable 0 (by simp)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12ee0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x112ee0 0x4c (by simp [RexWPrefix]) 7 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ee4 (by decide))
  advance_then (bswap_r64_effect_step 0x112ee4 14)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ee7 (by decide))
  advance_then (bswap_r64_effect_step 0x112ee7 15)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eea (by decide))
  advance_then (mov_r64_m64_effect_step 0x112eea 0x4c (by simp [RexWPrefix]) 4 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 13 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eee (by decide))
  advance_then (bswap_r64_effect_step 0x112eee 12)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ef1 (by decide))
  advance_then (mov_r64_r64_effect_step 0x112ef1 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ef4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x112ef4 0x4c (by simp [RexWPrefix]) 5 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ef8 (by decide))
  advance_then (bswap_r64_effect_step 0x112ef8 13)
  case sub => exact codeRange_slice_subset 0x112edd loadBytes 27 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12efb (by decide))
  advance_finish [loadEffect, BitVec.add_zero]

end P256.Proofs.Generate.Scalar
