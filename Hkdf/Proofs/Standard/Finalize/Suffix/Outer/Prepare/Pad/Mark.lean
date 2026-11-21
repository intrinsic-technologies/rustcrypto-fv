import Hkdf.Proofs.Common.StreamPadding.Stages.ZeroLength
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Memory
import X86Proofs.Instructions.Or.Generated.AccImm32.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Mark

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Instructions.ShiftLeft
open Hkdf.Proofs.Common.Instructions.CrossPageStore (Writable)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10df89
  readable : MemReadable s (rspOf s + 208) 8
  writable : ∀ i ∈ ([105,113,120,128] : List Nat),
    Writable s (rspOf s + BitVec.ofNat 64 i) 8
  marker : Writable s (rspOf s + 104) 1
  codeApart : ∀ i ∈ ([105,113,120,128] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 61 →
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8
        (0x10df89 + BitVec.ofNat 64 offset) len
  markerApart : ∀ offset len : Nat, offset + len ≤ 61 →
    RangeApart (rspOf s + 104) 1 (0x10df89 + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0xc6, 0x44, 0x24, 0x68, 0x80, 0x48, 0xc7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x71, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x69, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x09, 0x48, 0x0d, 0x00, 0x01, 0x00, 0x00, 0x48, 0x0f, 0xc8, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00]

def lengthWord (s : RamState) : BitVec 64 :=
  bswap64 ((memLoad s.external (rspOf s + 208) 64 <<< 9) ||| 256)

def effect (s : RamState) : Effect :=
  { rip := 0x10dfc6
    writes := [⟨(.reg 0 : Operand 64), lengthWord s⟩,
      ⟨(.mem (rspOf s + 104) : Operand 8), 128⟩,
      ⟨(.mem (rspOf s + 120) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 113) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 105) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 128) : Operand 64), lengthWord s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10df89 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xdf89 bytes
    (by decide +kernel) (by decide +kernel)

attribute [local x86_local] Hkdf.Proofs.Common.StreamPadding.Stages.shift64_local
attribute [local x86_compose] shlR64Effect
  external_write_mem external_write_reg external_after

set_option maxHeartbeats 3000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10df89 bytes) (Effect.post effect) := by
  have shift_nine : shiftCount 64 (UInt8.toBitVec 9) = 9 := rfl
  have zero_stores (m : Ram) (a b : BitVec 64) :
      memLoad (memStore (memStore m a 0#64) b 0#64) a 64 = 0#64 :=
    memLoad_zero_store _ a b (memLoad_memStore m a (by decide) (by decide) 0)
  advance_begin (mov_r64_m64_effect_step 0x10df89 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 208)) (by decide) rfl rfl)
  case pre => exact fun s h => ⟨h.rip,h.readable⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xdf91 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10df91 (.sib 4 none 0 (.d8 104))
    (by decide) rfl rfl 128)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact ⟨hP.marker.low, hP.marker.mem, hP.marker.tables⟩
    · x86_norm
      exact hP.markerApart 8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.markerApart 0 61 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdf96 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
    0x10df96 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 120))
    (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 13 9
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 (by decide)
    · x86_norm
      exact hP.codeApart 120 (by decide) 13 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 (by decide) 0 61 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdf9f (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
    0x10df9f 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 113))
    (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 22 9
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 113 (by decide)
    · x86_norm
      exact hP.codeApart 113 (by decide) 22 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 113 (by decide) 0 61 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfa8 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
    0x10dfa8 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 105))
    (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 31 9
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 105 (by decide)
    · x86_norm
      exact hP.codeApart 105 (by decide) 31 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 105 (by decide) 0 61 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfb1 (by decide))
  advance_then (StepEffect.forgetFlags (h := shl_r64_imm8_effect_step 0x10dfb1
    0x48 0xe0 9 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10df89 bytes 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, shlR64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfb5 (by decide))
  advance_then (StepEffect.forgetFlags (h := or_rax_imm32_effect_step 0x10dfb5
    0x48 256 (by simp [RexWPrefix])))
  case sub => exact codeRange_slice_subset 0x10df89 bytes 44 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, orRaxImm32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfbb (by decide))
  advance_then (bswap_r64_effect_step 0x10dfbb 0)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 50 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfbe (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfbe 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df89 bytes 53 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by decide)
    · x86_norm
      exact hP.codeApart 128 (by decide) 53 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by decide) 0 61 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfc6 (by decide))
  advance_finish [effect, lengthWord, shift_nine, zero_stores]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Mark
