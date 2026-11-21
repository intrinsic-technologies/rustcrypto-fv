import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Legacy

set_option autoImplicit false

open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open Hkdf.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] Hkdf.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10e020
  readable : ∀ i ∈ ([176,180,184,188,192,196,200,204] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([216,220,224,228,232,236,240,244] : List (BitVec 64)),
    Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s + i) 4
  codeApart : ∀ i ∈ ([216,220,224,228,232,236,240,244] : List (BitVec 64)),
    ∀ offset len : Nat, 0x10e020 ≤ offset → offset + len ≤ 0x10e0a9 →
    RangeApart (rspOf s + i) 4 (BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x8b, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0xb4, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0xb8, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0xbc, 0x0, 0x0, 0x0, 0xf, 0xce, 0x8b, 0xbc, 0x24, 0xc0, 0x0, 0x0, 0x0, 0xf, 0xcf, 0x44, 0x8b, 0x84, 0x24, 0xc4, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0xcc, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca, 0x89, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x89, 0x8c, 0x24, 0xdc, 0x0, 0x0, 0x0, 0x89, 0x94, 0x24, 0xe0, 0x0, 0x0, 0x0, 0x89, 0xb4, 0x24, 0xe4, 0x0, 0x0, 0x0, 0x89, 0xbc, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x44, 0x89, 0x84, 0x24, 0xec, 0x0, 0x0, 0x0, 0x44, 0x89, 0x8c, 0x24, 0xf0, 0x0, 0x0, 0x0, 0x44, 0x89, 0x94, 0x24, 0xf4, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10e0a9
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (rspOf s + 176) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (rspOf s + 180) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (rspOf s + 184) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (rspOf s + 188) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64),
        (bswap32 ((.mem (rspOf s + 192) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (rspOf s + 196) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (rspOf s + 200) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 10 : Operand 64),
        (bswap32 ((.mem (rspOf s + 204) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.mem (rspOf s + 216) : Operand 32),
        bswap32 ((.mem (rspOf s + 176) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 220) : Operand 32),
        bswap32 ((.mem (rspOf s + 180) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 224) : Operand 32),
        bswap32 ((.mem (rspOf s + 184) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 228) : Operand 32),
        bswap32 ((.mem (rspOf s + 188) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 232) : Operand 32),
        bswap32 ((.mem (rspOf s + 192) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 236) : Operand 32),
        bswap32 ((.mem (rspOf s + 196) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 240) : Operand 32),
        bswap32 ((.mem (rspOf s + 200) : Operand 32).read s)⟩,
      ⟨(.mem (rspOf s + 244) : Operand 32),
        bswap32 ((.mem (rspOf s + 204) : Operand 32).read s)⟩] }

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x10e020 ≤ ip → ip ≤ 0x10e0a9 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10e020 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x10e020 0 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 176 (by simp)⟩
  case next => intro s h; exact outside 0x10e027 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10e027 1 (.sib 4 none 0 (.d32 180)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 180 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10e02e (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e02e 0)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e030 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e030 1)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e032 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10e032 2 (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 184 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10e039 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e039 2)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e03b (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10e03b 6 (.sib 4 none 0 (.d32 188)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 188 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10e042 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e042 6)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e044 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x10e044 7 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 192 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x10e04b (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e04b 7)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e04d (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10e04d 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 196)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 196 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e055 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e055 8)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e058 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10e058 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 200 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e060 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e060 9)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e063 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x10e063 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 204)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 204 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x10e06b (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x10e06b 10)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x10e06e (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e06e 0 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 78 7
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 216 (by simp)
    · x86_norm
      exact hP.codeApart 216 (by simp) 0x10e06e 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 216 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e075 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e075 1 (.sib 4 none 0 (.d32 220)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 85 7
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 220 (by simp)
    · x86_norm
      exact hP.codeApart 220 (by simp) 0x10e075 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 220 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e07c (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e07c 2 (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 92 7
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 224 (by simp)
    · x86_norm
      exact hP.codeApart 224 (by simp) 0x10e07c 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 224 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e083 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e083 6 (.sib 4 none 0 (.d32 228)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 99 7
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 228 (by simp)
    · x86_norm
      exact hP.codeApart 228 (by simp) 0x10e083 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 228 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e08a (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e08a 7 (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 106 7
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 232 (by simp)
    · x86_norm
      exact hP.codeApart 232 (by simp) 0x10e08a 7 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 232 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e091 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10e091 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 236)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 113 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 236 (by simp)
    · x86_norm
      exact hP.codeApart 236 (by simp) 0x10e091 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 236 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e099 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10e099 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 121 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 240 (by simp)
    · x86_norm
      exact hP.codeApart 240 (by simp) 0x10e099 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 240 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e0a1 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10e0a1 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 244)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e020 bytes 129 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 244 (by simp)
    · x86_norm
      exact hP.codeApart 244 (by simp) 0x10e0a1 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 244 (by simp) 0x10e020 137 (by decide) (by decide)
    · exact outside 0x10e0a9 (by decide) (by decide)
  advance_finish [effect]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize
