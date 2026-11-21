import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Legacy

import X86Proofs.Instructions.Lea.Triple
import Hkdf.Proofs.Common.Memory
import Hkdf.Proofs.Common.SHA256.Words
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Serialization
import Hkdf.Spec.Program
import Hkdf.Proofs.Common.Machine.Code

set_option autoImplicit false

open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open Hkdf.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Serialize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] Hkdf.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10df0d
  readable : ∀ i ∈ ([136, 140, 144, 148, 152, 156, 160, 164] : List (BitVec 64)),
    MemReadable s (stackPtr s + i) 4
  writable : ∀ i ∈ ([72, 76, 80, 84, 88, 92, 96, 100] : List (BitVec 64)),
    Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + i) 4
  codeApart : ∀ i ∈ ([72, 76, 80, 84, 88, 92, 96, 100] : List (BitVec 64)),
    ∀ offset len : Nat, 0x10df0d ≤ offset → offset + len ≤ 0x10df89 →
    RangeApart (stackPtr s + i) 4 (BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0x8c, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0x90, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0x94, 0x0, 0x0, 0x0, 0xf, 0xce, 0x44, 0x8b, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0x9c, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca, 0x44, 0x8b, 0x9c, 0x24, 0xa4, 0x0, 0x0, 0x0, 0x41, 0xf, 0xcb, 0x48, 0x8d, 0xbc, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x89, 0x44, 0x24, 0x48, 0x89, 0x4c, 0x24, 0x4c, 0x89, 0x54, 0x24, 0x50, 0x89, 0x74, 0x24, 0x54, 0x44, 0x89, 0x44, 0x24, 0x58, 0x44, 0x89, 0x4c, 0x24, 0x5c, 0x44, 0x89, 0x54, 0x24, 0x60, 0x44, 0x89, 0x5c, 0x24, 0x64]

def effect (s : RamState) : Effect :=
  { rip := 0x10df89
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 136) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 140) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 144) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 148) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 152) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 156) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 10 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 160) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 11 : Operand 64),
        (bswap32 ((.mem (stackPtr s + 164) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 176⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 32),
        bswap32 ((.mem (stackPtr s + 136) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 76) : Operand 32),
        bswap32 ((.mem (stackPtr s + 140) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 80) : Operand 32),
        bswap32 ((.mem (stackPtr s + 144) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 84) : Operand 32),
        bswap32 ((.mem (stackPtr s + 148) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 88) : Operand 32),
        bswap32 ((.mem (stackPtr s + 152) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 92) : Operand 32),
        bswap32 ((.mem (stackPtr s + 156) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 96) : Operand 32),
        bswap32 ((.mem (stackPtr s + 160) : Operand 32).read s)⟩,
      ⟨(.mem (stackPtr s + 100) : Operand 32),
        bswap32 ((.mem (stackPtr s + 164) : Operand 32).read s)⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10df0d bytes) s :=
  Hkdf.Proofs.Common.Machine.programText_slice
    (Hkdf.Proofs.Common.Machine.programLoaded_codeIn loaded) 0xdf0d bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x10df0d ≤ ip → ip ≤ 0x10df89 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10df0d bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x10df0d 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 136 (by simp)⟩
  case next => intro s h; exact outside 0x10df14 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10df14 1 (.sib 4 none 0 (.d32 140)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 140 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10df1b (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df1b 0)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df1d (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df1d 1)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df1f (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10df1f 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10df26 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df26 2)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df28 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10df28 6 (.sib 4 none 0 (.d32 148)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 148 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10df2f (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df2f 6)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df31 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10df31 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10df39 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df39 8)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 44 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df3c (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10df3c 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 47 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 156 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10df44 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df44 9)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 55 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df47 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10df47 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 58 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 160 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10df4f (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df4f 10)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 66 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df52 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10df52 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 164)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 69 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 164 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10df5a (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10df5a 11)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 77 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10df5d (by decide) (by decide)
  advance_then (lea_r64_effect_step 0x10df5d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10df65 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10df65 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 88 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.codeApart 72 (by simp) 0x10df65 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df69 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10df69 1 (.sib 4 none 0 (.d8 76)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 92 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 76 (by simp)
    · x86_norm
      exact hP.codeApart 76 (by simp) 0x10df69 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 76 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df6d (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10df6d 2 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 96 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 (by simp)
    · x86_norm
      exact hP.codeApart 80 (by simp) 0x10df6d 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 80 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df71 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10df71 6 (.sib 4 none 0 (.d8 84)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 100 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 84 (by simp)
    · x86_norm
      exact hP.codeApart 84 (by simp) 0x10df71 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 84 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df75 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10df75 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 104 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      exact hP.codeApart 88 (by simp) 0x10df75 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df7a (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10df7a 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 92)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 109 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 92 (by simp)
    · x86_norm
      exact hP.codeApart 92 (by simp) 0x10df7a 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 92 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df7f (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10df7f 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 114 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 96 (by simp)
    · x86_norm
      exact hP.codeApart 96 (by simp) 0x10df7f 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 96 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df84 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10df84 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 100)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df0d bytes 119 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 100 (by simp)
    · x86_norm
      exact hP.codeApart 100 (by simp) 0x10df84 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 100 (by simp) 0x10df0d 124 (by decide) (by decide)
    · exact outside 0x10df89 (by decide) (by decide)
  advance_finish [effect]

open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.SHA256.Compression

theorem rsp_unchanged {s t : RamState} (h : (effect s).Holds s t) : stackPtr t = stackPtr s := by
  exact h.agrees.read (n := 64) (r := 4) (by simp [effect, Effect.components])

theorem payload {s t : RamState} {hash : Array UInt32}
    (pre : Pre s) (hashWords : HashStateAt s (stackPtr s + 136) hash)
    (h : (effect s).Holds s t) :
    (⟨(stackPtr s + 72).toNat, 32⟩ : MemoryRegion).HasBytes t.external (serializeHash hash) := by
  have allocated : ∀ i < 32, (t.external[stackPtr s + 72 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have hj : i / 4 < 8 := by omega
    have hw : MemReadable t (stackPtr s + 72 + BitVec.ofNat 64 (4 * (i / 4))) 4 := by
      apply MemReadable.of_holds h
      rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 ∨
        i / 4 = 4 ∨ i / 4 = 5 ∨ i / 4 = 6 ∨ i / 4 = 7) with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 72 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 76 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 80 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 84 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 88 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 92 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 96 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 100 (by simp)).toMemReadable
    have byte := hw.mem (i % 4) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * (i / 4) + i % 4 = i by omega] at byte
    exact byte
  have values : ∀ j < 8,
      memLoad s.external (stackPtr s + 136 + BitVec.ofNat 64 (4 * j)) 32 = hash[j]!.toBitVec := by
    intro j hj
    apply memLoad32_of_loadBytes4
    · intro k hk
      have hr : MemReadable s (stackPtr s + 136 + BitVec.ofNat 64 (4 * j)) 4 := by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 136 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 140 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 144 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 148 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 152 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 156 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 160 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 164 (by simp)
      exact hr.mem k hk
    · exact hashWords.2 j hj
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have words : ∀ j < 8, memLoad t.external
      (stackPtr s + 72 + BitVec.ofNat 64 (4 * j)) 32 = bswap32 hash[j]!.toBitVec := by
    intro j hj
    rw [← values j hj]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [stackPtr, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have bytes := Hkdf.Proofs.Common.Memory.bigEndian_bytes allocated words
  refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, hashWords.1], ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [serializeHash_size, hashWords.1] using i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr s + 72).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, serializeHash_getElem]
  exact bytes i.val hi

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Serialize
