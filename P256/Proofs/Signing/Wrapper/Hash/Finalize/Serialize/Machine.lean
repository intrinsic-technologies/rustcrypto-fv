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
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable mov_m32_r32_legacy_effect_step_any mov_m32_r32_effect_step_any)
open P256.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] P256.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1029a9
  readable : ∀ i ∈ ([128,132,136,140,144,148,152,156] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    Writable s (rspOf s + i) 4
  codeApart : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 4 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x8b,0x8c,0x24,0x84,0x0,0x0,0x0,0xf,0xc8,0xf,0xc9,0x8b,0x94,0x24,0x88,0x0,0x0,0x0,0xf,0xca,0x8b,0xb4,0x24,0x8c,0x0,0x0,0x0,0xf,0xce,0x8b,0xbc,0x24,0x90,0x0,0x0,0x0,0xf,0xcf,0x44,0x8b,0x84,0x24,0x94,0x0,0x0,0x0,0x41,0xf,0xc8,0x44,0x8b,0x8c,0x24,0x98,0x0,0x0,0x0,0x41,0xf,0xc9,0x44,0x8b,0x94,0x24,0x9c,0x0,0x0,0x0,0x41,0xf,0xca,0x89,0x4,0x24,0x89,0x4c,0x24,0x4,0x89,0x54,0x24,0x8,0x89,0x74,0x24,0xc,0x89,0x7c,0x24,0x10,0x44,0x89,0x44,0x24,0x14,0x44,0x89,0x4c,0x24,0x18,0x44,0x89,0x54,0x24,0x1c]

def effect (s : RamState) : Effect :=
  { rip := 0x102a19
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (rspOf s + 128) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (rspOf s + 132) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (rspOf s + 136) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (rspOf s + 140) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64),
        (bswap32 ((.mem (rspOf s + 144) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (rspOf s + 148) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (rspOf s + 152) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 10 : Operand 64),
        (bswap32 ((.mem (rspOf s + 156) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.mem (rspOf s + 0) : Operand 32),
        bswap32 ((.mem (rspOf s + 128) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 4) : Operand 32),
        bswap32 ((.mem (rspOf s + 132) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 8) : Operand 32),
        bswap32 ((.mem (rspOf s + 136) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 12) : Operand 32),
        bswap32 ((.mem (rspOf s + 140) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 16) : Operand 32),
        bswap32 ((.mem (rspOf s + 144) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 20) : Operand 32),
        bswap32 ((.mem (rspOf s + 148) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 24) : Operand 32),
        bswap32 ((.mem (rspOf s + 152) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 28) : Operand 32),
        bswap32 ((.mem (rspOf s + 156) : Operand 32).read s)⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1029a9 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x29a9 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1029a9 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x1029a9 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 128 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x29b0 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1029b0 1 (.sib 4 none 0 (.d32 132)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 132 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29b7 (by decide))
  advance_then (bswap_r32_effect_step 0x1029b7 0)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29b9 (by decide))
  advance_then (bswap_r32_effect_step 0x1029b9 1)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29bb (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1029bb 2 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29c2 (by decide))
  advance_then (bswap_r32_effect_step 0x1029c2 2)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29c4 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1029c4 6 (.sib 4 none 0 (.d32 140)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 140 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29cb (by decide))
  advance_then (bswap_r32_effect_step 0x1029cb 6)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29cd (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x1029cd 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29d4 (by decide))
  advance_then (bswap_r32_effect_step 0x1029d4 7)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29d6 (by decide))
  advance_then (mov_r32_m32_effect_step 0x1029d6 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 148)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 148 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29de (by decide))
  advance_then (bswap_r32_effect_step 0x1029de 8)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29e1 (by decide))
  advance_then (mov_r32_m32_effect_step 0x1029e1 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29e9 (by decide))
  advance_then (bswap_r32_effect_step 0x1029e9 9)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29ec (by decide))
  advance_then (mov_r32_m32_effect_step 0x1029ec 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 156 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29f4 (by decide))
  advance_then (bswap_r32_effect_step 0x1029f4 10)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29f7 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x1029f7 0 (.sib 4 none 0 .none)) from mov_m32_r32_legacy_effect_step_any 0x1029f7 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 78 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x29f7 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29fa (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x1029fa 1 (.sib 4 none 0 (.d8 4))) from mov_m32_r32_legacy_effect_step_any 0x1029fa 1 (.sib 4 none 0 (.d8 4)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 81 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by simp)
    · x86_norm
      exact hP.codeApart 4 (by simp) 0x29fa 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 4 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x29fe (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x1029fe 2 (.sib 4 none 0 (.d8 8))) from mov_m32_r32_legacy_effect_step_any 0x1029fe 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 85 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x29fe 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a02 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x102a02 6 (.sib 4 none 0 (.d8 12))) from mov_m32_r32_legacy_effect_step_any 0x102a02 6 (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 89 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 12 (by simp)
    · x86_norm
      exact hP.codeApart 12 (by simp) 0x2a02 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 12 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a06 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x102a06 7 (.sib 4 none 0 (.d8 16))) from mov_m32_r32_legacy_effect_step_any 0x102a06 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 93 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x2a06 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a0a (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x102a0a 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 20)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 97 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 20 (by simp)
    · x86_norm
      exact hP.codeApart 20 (by simp) 0x2a0a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 20 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a0f (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x102a0f 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 102 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x2a0f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a14 (by decide))
  advance_then (mov_m32_r32_effect_step_any 0x102a14 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 28)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1029a9 bytes 107 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 28 (by simp)
    · x86_norm
      exact hP.codeApart 28 (by simp) 0x2a14 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 28 (by simp) 0x29a9 112 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a19 (by decide))
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize
