import Sha2.Proofs.Wrapper.Variant
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
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.Encoding.Serialize.Store32
import Sha2.Proofs.Common.Instructions.CrossPageStore.Compose

set_option autoImplicit false

open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open Sha2.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open Sha2.Proofs.Common.Instructions (mov_m32_r32_no_rex_effect_step)
open Sha2.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace Sha2.Proofs.Wrapper.Hash.Serialize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] Sha2.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

def outputAddress (s : RamState) : BitVec 64 :=
  memLoad s.external (rspOf s + 168) 64

attribute [local x86_compose] outputAddress Variant.pc Variant.textOffset

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = v.pc 0x332
  readable : ∀ i ∈ ([64,68,72,76,80,84,88,92] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  pointer : MemReadable s (rspOf s + 168) 8
  writable : ∀ i ∈ (([0,4,8,12,16,20,24,28] : List (BitVec 64)).take (v.outputBytes / 4)),
    Common.Instructions.CrossPageStore.Writable s (outputAddress s + i) 4
  codeApart : ∀ i ∈ (([0,4,8,12,16,20,24,28] : List (BitVec 64)).take (v.outputBytes / 4)),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (outputAddress s + i) 4 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes (v : Variant := .sha256) : List UInt8 :=
  match v with
  | .sha224 => [0x8b, 0x44, 0x24, 0x40, 0x8b, 0x4c, 0x24, 0x44, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x54, 0x24, 0x48, 0xf, 0xca, 0x8b, 0x74, 0x24, 0x4c, 0xf, 0xce, 0x8b, 0x7c, 0x24, 0x50, 0xf, 0xcf, 0x44, 0x8b, 0x44, 0x24, 0x54, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0xf, 0xc9, 0x4c, 0x8b, 0x94, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x41, 0x89, 0x2, 0x41, 0x89, 0x4a, 0x4, 0x41, 0x89, 0x52, 0x8, 0x41, 0x89, 0x72, 0xc, 0x41, 0x89, 0x7a, 0x10, 0x45, 0x89, 0x42, 0x14, 0x45, 0x89, 0x4a, 0x18]
  | .sha256 => [0x8b, 0x44, 0x24, 0x40, 0x8b, 0x4c, 0x24, 0x44, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x54, 0x24, 0x48, 0xf, 0xca, 0x8b, 0x74, 0x24, 0x4c, 0xf, 0xce, 0x8b, 0x7c, 0x24, 0x50, 0xf, 0xcf, 0x44, 0x8b, 0x44, 0x24, 0x54, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x54, 0x24, 0x5c, 0x41, 0xf, 0xca, 0x4c, 0x8b, 0x9c, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x41, 0x89, 0x3, 0x41, 0x89, 0x4b, 0x4, 0x41, 0x89, 0x53, 0x8, 0x41, 0x89, 0x73, 0xc, 0x41, 0x89, 0x7b, 0x10, 0x45, 0x89, 0x43, 0x14, 0x45, 0x89, 0x4b, 0x18, 0x45, 0x89, 0x53, 0x1c]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := v.pc v.epilogueOffset
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (rspOf s + 64) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (rspOf s + 68) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (rspOf s + 72) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (rspOf s + 76) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64),
        (bswap32 ((.mem (rspOf s + 80) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (rspOf s + 84) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (rspOf s + 88) : Operand 32).read s)).setWidth 64⟩
      ] ++ (match v with
        | .sha224 => [⟨(.reg 10 : Operand 64), outputAddress s⟩]
        | .sha256 => [⟨(.reg 10 : Operand 64),
            (bswap32 ((.mem (rspOf s + 92) : Operand 32).read s)).setWidth 64⟩,
            ⟨(.reg 11 : Operand 64), outputAddress s⟩]) ++ [
      ⟨(.mem (outputAddress s + 0) : Operand 32),
        bswap32 ((.mem (rspOf s + 64) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 4) : Operand 32),
        bswap32 ((.mem (rspOf s + 68) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 8) : Operand 32),
        bswap32 ((.mem (rspOf s + 72) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 12) : Operand 32),
        bswap32 ((.mem (rspOf s + 76) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 16) : Operand 32),
        bswap32 ((.mem (rspOf s + 80) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 20) : Operand 32),
        bswap32 ((.mem (rspOf s + 84) : Operand 32).read s)⟩,
      ⟨(.mem (outputAddress s + 24) : Operand 32),
        bswap32 ((.mem (rspOf s + 88) : Operand 32).read s)⟩] ++ (match v with
        | .sha224 => []
        | .sha256 => [
      ⟨(.mem (outputAddress s + 28) : Operand 32),
        bswap32 ((.mem (rspOf s + 92) : Operand 32).read s)⟩]) }

theorem code {s : RamState} (loaded : ProgramLoaded s) (v : Variant := .sha256) :
    CodeIn (codeRange (v.pc 0x332) (bytes v)) s := by
  cases v <;> exact programText_slice (programLoaded_codeIn loaded) _ _
    (by decide +kernel) (by decide +kernel)

local macro "serialize_prefix " v:term "," o:term : tactic => `(tactic| (
  advance_begin (mov_r32_m32_legacy_effect_step (($v).pc 0x332) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 64 (by decide +kernel)⟩
  case next =>
    intro s h
    exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x336) (by decide))
  advance_then (mov_r32_m32_legacy_effect_step (($v).pc 0x336) 1 (.sib 4 none 0 (.d8 68)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 68 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x33a) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x33a) 0)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 8 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x33c) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x33c) 1)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x33e) (by decide))
  advance_then (mov_r32_m32_legacy_effect_step (($v).pc 0x33e) 2 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x342) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x342) 2)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x344) (by decide))
  advance_then (mov_r32_m32_legacy_effect_step (($v).pc 0x344) 6 (.sib 4 none 0 (.d8 76)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 76 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x348) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x348) 6)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 22 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x34a) (by decide))
  advance_then (mov_r32_m32_legacy_effect_step (($v).pc 0x34a) 7 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 80 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x34e) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x34e) 7)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 28 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x350) (by decide))
  advance_then (mov_r32_m32_effect_step (($v).pc 0x350) 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 84)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 84 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x355) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x355) 8)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 35 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x358) (by decide))
  advance_then (mov_r32_m32_effect_step (($v).pc 0x358) 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x35d) (by decide))
  advance_then (bswap_r32_effect_step (($v).pc 0x35d) 9)
  case sub => exact codeRange_slice_subset (($v).pc 0x332) (bytes $v) 43 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program $o (Variant.pc_inProgram $v (offset := 0x360) (by decide))
))

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (v : Variant := .sha256) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x332) (bytes v))
      (Effect.post (fun s => effect s v)) := by
  cases v with
  | sha224 =>
    serialize_prefix Variant.sha224, outside
    advance_then (mov_r64_m64_effect_step 0x100610 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 46 8
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm
        exact hP.pointer
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x618 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x100618 0x41 (by simp [RexNoWPrefix]) 0 (.base 10 .none) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 54 3
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 0 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 0 (by decide +kernel) 0x618 3 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 0 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61b (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10061b 0x41 (by simp [RexNoWPrefix]) 1 (.base 10 (.d8 4)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 57 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 4 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 4 (by decide +kernel) 0x61b 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 4 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61f (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10061f 0x41 (by simp [RexNoWPrefix]) 2 (.base 10 (.d8 8)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 61 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 8 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 8 (by decide +kernel) 0x61f 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 8 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x623 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x100623 0x41 (by simp [RexNoWPrefix]) 6 (.base 10 (.d8 12)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 65 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 12 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 12 (by decide +kernel) 0x623 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 12 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x627 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x100627 0x41 (by simp [RexNoWPrefix]) 7 (.base 10 (.d8 16)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 69 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 16 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 16 (by decide +kernel) 0x627 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 16 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x62b (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10062b 0x45 (by simp [RexNoWPrefix]) 0 (.base 10 (.d8 20)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 73 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 20 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 20 (by decide +kernel) 0x62b 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 20 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x62f (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10062f 0x45 (by simp [RexNoWPrefix]) 1 (.base 10 (.d8 24)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1005e2 (bytes .sha224) 77 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 24 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 24 (by decide +kernel) 0x62f 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 24 (by decide +kernel) 0x5e2 81 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x633 (by decide))
    advance_finish [effect, outputAddress, Variant.pc, Variant.textOffset, Variant.epilogueOffset]
  | sha256 =>
    serialize_prefix Variant.sha256, outside
    advance_then (mov_r32_m32_effect_step 0x102210 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 92)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 46 5
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm
        exact hP.readable 92 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2215 (by decide))
    advance_then (bswap_r32_effect_step 0x102215 10)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 51 3
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers, Sha2.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2218 (by decide))
    advance_then (mov_r64_m64_effect_step 0x102218 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 54 8
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm
        exact hP.pointer
      · apply Effect.Avoids.of_noMem
        simp [Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2220 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x102220 0x41 (by simp [RexNoWPrefix]) 0 (.base 11 .none) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 62 3
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 0 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 0 (by decide +kernel) 0x2220 3 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 0 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2223 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x102223 0x41 (by simp [RexNoWPrefix]) 1 (.base 11 (.d8 4)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 65 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 4 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 4 (by decide +kernel) 0x2223 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 4 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2227 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x102227 0x41 (by simp [RexNoWPrefix]) 2 (.base 11 (.d8 8)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 69 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 8 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 8 (by decide +kernel) 0x2227 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 8 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x222b (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10222b 0x41 (by simp [RexNoWPrefix]) 6 (.base 11 (.d8 12)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 73 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 12 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 12 (by decide +kernel) 0x222b 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 12 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x222f (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10222f 0x41 (by simp [RexNoWPrefix]) 7 (.base 11 (.d8 16)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 77 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 16 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 16 (by decide +kernel) 0x222f 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 16 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2233 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x102233 0x45 (by simp [RexNoWPrefix]) 0 (.base 11 (.d8 20)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 81 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 20 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 20 (by decide +kernel) 0x2233 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 20 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x2237 (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x102237 0x45 (by simp [RexNoWPrefix]) 1 (.base 11 (.d8 24)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 85 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 24 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 24 (by decide +kernel) 0x2237 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 24 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x223b (by decide))
    advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10223b 0x45 (by simp [RexNoWPrefix]) 2 (.base 11 (.d8 28)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset 0x1021e2 (bytes .sha256) 89 4
    case mid =>
      intro s t hP hH hO
      refine ⟨Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 28 (by decide +kernel)
      · x86_norm
        exact hP.codeApart 28 (by decide +kernel) 0x223b 4 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 28 (by decide +kernel) 0x21e2 93 (by decide)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x223f (by decide))
    advance_finish [effect, outputAddress, Variant.pc, Variant.textOffset, Variant.epilogueOffset]

end Sha2.Proofs.Wrapper.Hash.Serialize
