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

namespace Hkdf.Proofs.Key.Hash.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] Hkdf.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1165c9
  readable : ∀ i ∈ ([128,132,136,140,144,148,152,156] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s + i) 4
  codeApart : ∀ i ∈ ([0,4,8,12,16,20,24,28] : List (BitVec 64)),
    ∀ offset len : Nat, 0x1165c9 ≤ offset → offset + len ≤ 0x116639 →
    RangeApart (rspOf s + i) 4 (BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x8b, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0x84, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0x88, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0x8c, 0x0, 0x0, 0x0, 0xf, 0xce, 0x8b, 0xbc, 0x24, 0x90, 0x0, 0x0, 0x0, 0xf, 0xcf, 0x44, 0x8b, 0x84, 0x24, 0x94, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0x98, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0x9c, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca, 0x89, 0x4, 0x24, 0x89, 0x4c, 0x24, 0x4, 0x89, 0x54, 0x24, 0x8, 0x89, 0x74, 0x24, 0xc, 0x89, 0x7c, 0x24, 0x10, 0x44, 0x89, 0x44, 0x24, 0x14, 0x44, 0x89, 0x4c, 0x24, 0x18, 0x44, 0x89, 0x54, 0x24, 0x1c]

def effect (s : RamState) : Effect :=
  { rip := 0x116639
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

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : Nat, 0x1165c9 ≤ ip → ip ≤ 0x116639 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1165c9 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x1165c9 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 128 (by simp)⟩
  case next => intro s h; exact outside 0x1165d0 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x1165d0 1 (.sib 4 none 0 (.d32 132)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 132 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x1165d7 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165d7 0)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x1165d9 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165d9 1)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x1165db (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x1165db 2 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x1165e2 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165e2 2)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x1165e4 (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x1165e4 6 (.sib 4 none 0 (.d32 140)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 140 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x1165eb (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165eb 6)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x1165ed (by decide) (by decide)
  advance_then (mov_r32_m32_legacy_effect_step 0x1165ed 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact outside 0x1165f4 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165f4 7)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x1165f6 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x1165f6 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 148)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 148 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x1165fe (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x1165fe 8)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x116601 (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x116601 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x116609 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x116609 9)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x11660c (by decide) (by decide)
  advance_then (mov_r32_m32_effect_step 0x11660c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 156 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 0x116614 (by decide) (by decide)
  advance_then (bswap_r32_effect_step 0x116614 10)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Hkdf.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact outside 0x116617 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x116617 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 78 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x116617 3 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x11661a (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x11661a 1 (.sib 4 none 0 (.d8 4)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 81 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by simp)
    · x86_norm
      exact hP.codeApart 4 (by simp) 0x11661a 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 4 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x11661e (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x11661e 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 85 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x11661e 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x116622 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x116622 6 (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 89 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 12 (by simp)
    · x86_norm
      exact hP.codeApart 12 (by simp) 0x116622 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 12 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x116626 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x116626 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 93 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x116626 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x11662a (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x11662a 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 20)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 97 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 20 (by simp)
    · x86_norm
      exact hP.codeApart 20 (by simp) 0x11662a 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 20 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x11662f (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x11662f 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 102 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x11662f 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x116634 (by decide) (by decide)
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x116634 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 28)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1165c9 bytes 107 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 28 (by simp)
    · x86_norm
      exact hP.codeApart 28 (by simp) 0x116634 5 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 28 (by simp) 0x1165c9 112 (by decide) (by decide)
    · exact outside 0x116639 (by decide) (by decide)
  advance_finish [effect]

end Hkdf.Proofs.Key.Hash.Serialize
