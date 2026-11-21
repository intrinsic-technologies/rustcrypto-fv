import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Instructions.LegacyLoad

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable mov_m32_r32_legacy_effect_step_any mov_m32_r32_effect_step_any)
open P256.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace P256.Proofs.Verifying.Message.Hash.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] P256.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d8ce
  readable : ∀ i ∈ ([192,196,200,204,208,212,216,220] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([424,428,432,436,440,444,448,452] : List (BitVec 64)),
    Writable s (rspOf s + i) 4
  codeApart : ∀ i ∈ ([424,428,432,436,440,444,448,452] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 4 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x8b,0x84,0x24,0xc0,0x0,0x0,0x0,0x8b,0x8c,0x24,0xc4,0x0,0x0,0x0,0xf,0xc8,0xf,0xc9,0x8b,0x94,0x24,0xc8,0x0,0x0,0x0,0xf,0xca,0x8b,0xb4,0x24,0xcc,0x0,0x0,0x0,0xf,0xce,0x8b,0xbc,0x24,0xd0,0x0,0x0,0x0,0xf,0xcf,0x44,0x8b,0x84,0x24,0xd4,0x0,0x0,0x0,0x41,0xf,0xc8,0x44,0x8b,0x8c,0x24,0xd8,0x0,0x0,0x0,0x41,0xf,0xc9,0x44,0x8b,0x94,0x24,0xdc,0x0,0x0,0x0,0x41,0xf,0xca,0x89,0x84,0x24,0xa8,0x1,0x0,0x0,0x89,0x8c,0x24,0xac,0x1,0x0,0x0,0x89,0x94,0x24,0xb0,0x1,0x0,0x0,0x89,0xb4,0x24,0xb4,0x1,0x0,0x0,0x89,0xbc,0x24,0xb8,0x1,0x0,0x0,0x44,0x89,0x84,0x24,0xbc,0x1,0x0,0x0,0x44,0x89,0x8c,0x24,0xc0,0x1,0x0,0x0,0x44,0x89,0x94,0x24,0xc4,0x1,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10d957
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (rspOf s + 192) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (rspOf s + 196) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (rspOf s + 200) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (rspOf s + 204) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64),
        (bswap32 ((.mem (rspOf s + 208) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (rspOf s + 212) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (rspOf s + 216) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 10 : Operand 64),
        (bswap32 ((.mem (rspOf s + 220) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.mem (rspOf s + 424) : Operand 32),
        bswap32 ((.mem (rspOf s + 192) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 428) : Operand 32),
        bswap32 ((.mem (rspOf s + 196) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 432) : Operand 32),
        bswap32 ((.mem (rspOf s + 200) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 436) : Operand 32),
        bswap32 ((.mem (rspOf s + 204) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 440) : Operand 32),
        bswap32 ((.mem (rspOf s + 208) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 444) : Operand 32),
        bswap32 ((.mem (rspOf s + 212) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 448) : Operand 32),
        bswap32 ((.mem (rspOf s + 216) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 452) : Operand 32),
        bswap32 ((.mem (rspOf s + 220) : Operand 32).read s)⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d8ce bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd8ce bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d8ce bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x10d8ce 0 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 192 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd8d5 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10d8d5 1 (.sib 4 none 0 (.d32 196)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 196 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8dc (by decide))
  advance_then (bswap_r32_effect_step 0x10d8dc 0)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8de (by decide))
  advance_then (bswap_r32_effect_step 0x10d8de 1)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8e0 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10d8e0 2 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 200 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8e7 (by decide))
  advance_then (bswap_r32_effect_step 0x10d8e7 2)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8e9 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10d8e9 6 (.sib 4 none 0 (.d32 204)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 204 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8f0 (by decide))
  advance_then (bswap_r32_effect_step 0x10d8f0 6)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8f2 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10d8f2 7 (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 208 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8f9 (by decide))
  advance_then (bswap_r32_effect_step 0x10d8f9 7)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd8fb (by decide))
  advance_then (mov_r32_m32_effect_step 0x10d8fb 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 212)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 212 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd903 (by decide))
  advance_then (bswap_r32_effect_step 0x10d903 8)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd906 (by decide))
  advance_then (mov_r32_m32_effect_step 0x10d906 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 216 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd90e (by decide))
  advance_then (bswap_r32_effect_step 0x10d90e 9)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd911 (by decide))
  advance_then (mov_r32_m32_effect_step 0x10d911 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 220)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 220 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd919 (by decide))
  advance_then (bswap_r32_effect_step 0x10d919 10)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd91c (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10d91c 0 (.sib 4 none 0 (.d32 424))) from mov_m32_r32_legacy_effect_step_any 0x10d91c 0 (.sib 4 none 0 (.d32 424)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 78 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 424 (by simp)
    · x86_norm
      exact hP.codeApart 424 (by simp) 0xd91c 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 424 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd923 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10d923 1 (.sib 4 none 0 (.d32 428))) from mov_m32_r32_legacy_effect_step_any 0x10d923 1 (.sib 4 none 0 (.d32 428)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 85 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 428 (by simp)
    · x86_norm
      exact hP.codeApart 428 (by simp) 0xd923 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 428 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd92a (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10d92a 2 (.sib 4 none 0 (.d32 432))) from mov_m32_r32_legacy_effect_step_any 0x10d92a 2 (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 92 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 432 (by simp)
    · x86_norm
      exact hP.codeApart 432 (by simp) 0xd92a 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 432 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd931 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10d931 6 (.sib 4 none 0 (.d32 436))) from mov_m32_r32_legacy_effect_step_any 0x10d931 6 (.sib 4 none 0 (.d32 436)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 99 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 436 (by simp)
    · x86_norm
      exact hP.codeApart 436 (by simp) 0xd931 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 436 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd938 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10d938 7 (.sib 4 none 0 (.d32 440))) from mov_m32_r32_legacy_effect_step_any 0x10d938 7 (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 106 7
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 440 (by simp)
    · x86_norm
      exact hP.codeApart 440 (by simp) 0xd938 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 440 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd93f (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x10d93f 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 444)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 113 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 444 (by simp)
    · x86_norm
      exact hP.codeApart 444 (by simp) 0xd93f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 444 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd947 (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x10d947 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 448)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 121 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 448 (by simp)
    · x86_norm
      exact hP.codeApart 448 (by simp) 0xd947 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 448 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd94f (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x10d94f 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 452)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d8ce bytes 129 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 452 (by simp)
    · x86_norm
      exact hP.codeApart 452 (by simp) 0xd94f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 452 (by simp) 0xd8ce 137 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd957 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Message.Hash.Serialize
