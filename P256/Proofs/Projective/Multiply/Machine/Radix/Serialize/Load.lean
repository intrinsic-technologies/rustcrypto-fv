import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
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
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (bswap64 bswapR64Effect bswap_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x112ea0
  readable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8

def loadBytes : List UInt8 :=
  [0x48, 0x8b, 0x4e, 0x18, 0x48, 0x0f, 0xc9, 0x48, 0x8b, 0x56, 0x10,
    0x48, 0x0f, 0xca, 0x48, 0x89, 0xf8, 0x48, 0x8b, 0x7e, 0x08,
    0x48, 0x0f, 0xcf, 0x48, 0x8b, 0x36, 0x48, 0x0f, 0xce]

def loadEffect (s : RamState) : Effect :=
  { rip := 0x112ebe
    writes := [
      ⟨(Operand.reg 1 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 24) :
          Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) :
          Operand 64).read s)⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) :
          Operand 64).read s)⟩,
      ⟨(Operand.reg 6 : Operand 64),
        bswap64 ((Operand.mem ((Operand.reg 6 : Operand 64).read s) :
          Operand 64).read s)⟩] }

theorem load_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x112ea0 loadBytes)
      (Effect.post loadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x112ea0 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 6 (.d8 24))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 24 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12ea4 (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x112ea4 1)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ea7 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x112ea7 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 6 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eab (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x112eab 2)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eae (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x112eae 0x48 0xf8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eb1 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x112eb1 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.base 6 (.d8 8))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 17 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eb5 (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x112eb5 7)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12eb8 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x112eb8 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 6 .none)
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 24 3
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ebb (by decide +kernel))
  advance_then (bswap_r64_effect_step 0x112ebb 6)
  case sub => exact codeRange_slice_subset 0x112ea0 loadBytes 27 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ebe (by decide +kernel))
  advance_finish [loadEffect, BitVec.add_zero]

end P256.Proofs.Projective.Multiply.Machine.Radix.Serialize
