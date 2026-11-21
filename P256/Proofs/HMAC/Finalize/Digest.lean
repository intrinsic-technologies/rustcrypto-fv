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
import P256.Proofs.SHA256.Memory.Serialization
import P256.Proofs.SHA256.Mathematics.Padding.Standard.Serialization

open P256.Proofs.Program

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Common.SHA256.Compression (bswap32 bswap_r32_effect_step)
open P256.Proofs.Common.Instructions.LegacyLoad (mov_r32_m32_legacy_effect_step)

namespace P256.Proofs.HMAC.Finalize.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] P256.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber

structure DigestPre (s : RamState) : Prop where
  rip : s.RIP = 0x101111
  readable : ∀ i ∈ ([136,140,144,148,152,156,160,164] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 4
  writable : ∀ i ∈ ([8,12,16,20,24,28,32,36] : List (BitVec 64)),
    Common.Instructions.CrossPageStore.Writable s (rspOf s + i) 4
  codeApart : ∀ i ∈ ([8,12,16,20,24,28,32,36] : List (BitVec 64)),
    RangeApart (rspOf s + i) 4 0x101111 113

theorem DigestPre.codeApart_slice {s : RamState} (h : DigestPre s)
    (i : BitVec 64) (hi : i ∈ [8,12,16,20,24,28,32,36])
    (offset len : Nat) (bound : offset + len ≤ 113) :
    RangeApart (rspOf s + i) 4 (0x101111 + BitVec.ofNat 64 offset) len := by
  intro j hj k hk
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    h.codeApart i hi j hj (offset + k) (by omega)

def bytes : List UInt8 :=
  [0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0x8c, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0x90, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0x94, 0x0, 0x0, 0x0, 0xf, 0xce, 0x8b, 0xbc, 0x24, 0x98, 0x0, 0x0, 0x0, 0xf, 0xcf, 0x44, 0x8b, 0x84, 0x24, 0x9c, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0xa4, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca, 0x89, 0x44, 0x24, 0x8, 0x89, 0x4c, 0x24, 0xc, 0x89, 0x54, 0x24, 0x10, 0x89, 0x74, 0x24, 0x14, 0x89, 0x7c, 0x24, 0x18, 0x44, 0x89, 0x44, 0x24, 0x1c, 0x44, 0x89, 0x4c, 0x24, 0x20, 0x44, 0x89, 0x54, 0x24, 0x24]

def serializeEffect (next destination : BitVec 64) (s : RamState) : Effect :=
  { rip := next
    writes := [
      ⟨(.reg 0 : Operand 64),
        (bswap32 ((.mem (rspOf s + 136) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 1 : Operand 64),
        (bswap32 ((.mem (rspOf s + 140) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64),
        (bswap32 ((.mem (rspOf s + 144) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),
        (bswap32 ((.mem (rspOf s + 148) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64),
        (bswap32 ((.mem (rspOf s + 152) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 8 : Operand 64),
        (bswap32 ((.mem (rspOf s + 156) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 9 : Operand 64),
        (bswap32 ((.mem (rspOf s + 160) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.reg 10 : Operand 64),
        (bswap32 ((.mem (rspOf s + 164) : Operand 32).read s)).setWidth 64⟩,
      ⟨(.mem (destination + 0) : Operand 32),
        bswap32 ((.mem (rspOf s + 136) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 4) : Operand 32),
        bswap32 ((.mem (rspOf s + 140) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 8) : Operand 32),
        bswap32 ((.mem (rspOf s + 144) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 12) : Operand 32),
        bswap32 ((.mem (rspOf s + 148) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 16) : Operand 32),
        bswap32 ((.mem (rspOf s + 152) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 20) : Operand 32),
        bswap32 ((.mem (rspOf s + 156) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 24) : Operand 32),
        bswap32 ((.mem (rspOf s + 160) : Operand 32).read s)⟩,
      ⟨(.mem (destination + 28) : Operand 32),
        bswap32 ((.mem (rspOf s + 164) : Operand 32).read s)⟩] }

def effect (s : RamState) : Effect :=
  serializeEffect 0x101182 (rspOf s + 8) s

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x101111 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1111 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DigestPre (codeRange 0x101111 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x101111 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 136 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1118 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x101118 1 (.sib 4 none 0 (.d32 140)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 7 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 140 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x111f (by decide))
  advance_then (bswap_r32_effect_step 0x10111f 0)
  case sub => exact codeRange_slice_subset 0x101111 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1121 (by decide))
  advance_then (bswap_r32_effect_step 0x101121 1)
  case sub => exact codeRange_slice_subset 0x101111 bytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1123 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x101123 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 18 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x112a (by decide))
  advance_then (bswap_r32_effect_step 0x10112a 2)
  case sub => exact codeRange_slice_subset 0x101111 bytes 25 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x112c (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10112c 6 (.sib 4 none 0 (.d32 148)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 27 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 148 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1133 (by decide))
  advance_then (bswap_r32_effect_step 0x101133 6)
  case sub => exact codeRange_slice_subset 0x101111 bytes 34 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1135 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x101135 7 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 36 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.LegacyLoad.movR32M32LegacyEffect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x113c (by decide))
  advance_then (bswap_r32_effect_step 0x10113c 7)
  case sub => exact codeRange_slice_subset 0x101111 bytes 43 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x113e (by decide))
  advance_then (mov_r32_m32_effect_step 0x10113e 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 156 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1146 (by decide))
  advance_then (bswap_r32_effect_step 0x101146 8)
  case sub => exact codeRange_slice_subset 0x101111 bytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1149 (by decide))
  advance_then (mov_r32_m32_effect_step 0x101149 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 160 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1151 (by decide))
  advance_then (bswap_r32_effect_step 0x101151 9)
  case sub => exact codeRange_slice_subset 0x101111 bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1154 (by decide))
  advance_then (mov_r32_m32_effect_step 0x101154 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 164)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 164 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x115c (by decide))
  advance_then (bswap_r32_effect_step 0x10115c 10)
  case sub => exact codeRange_slice_subset 0x101111 bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.SHA256.Compression.bswapR32Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x115f (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10115f 0 (.sib 4 none 0 (.d8 8))) from Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10115f 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 78 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart_slice 8 (by simp) 78 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1163 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x101163 1 (.sib 4 none 0 (.d8 12))) from Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x101163 1 (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 82 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 12 (by simp)
    · x86_norm
      exact hP.codeApart_slice 12 (by simp) 82 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 12 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1167 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x101167 2 (.sib 4 none 0 (.d8 16))) from Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x101167 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 86 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart_slice 16 (by simp) 86 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x116b (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10116b 6 (.sib 4 none 0 (.d8 20))) from Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10116b 6 (.sib 4 none 0 (.d8 20)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 90 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 20 (by simp)
    · x86_norm
      exact hP.codeApart_slice 20 (by simp) 90 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 20 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x116f (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.CrossPageStore.movM32R32LegacyEffect 0x10116f 7 (.sib 4 none 0 (.d8 24))) from Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10116f 7 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 94 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart_slice 24 (by simp) 94 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1173 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x101173 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 28)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 98 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 28 (by simp)
    · x86_norm
      exact hP.codeApart_slice 28 (by simp) 98 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 28 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1178 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x101178 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 103 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart_slice 32 (by simp) 103 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x117d (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x10117d 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 36)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101111 bytes 108 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 36 (by simp)
    · x86_norm
      exact hP.codeApart_slice 36 (by simp) 108 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 36 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1182 (by decide))
  advance_finish [effect, serializeEffect]

theorem serializeEffect_output {s t : RamState} {hash : Array UInt32}
    {next destination : BitVec 64}
    (sourceReadable : ∀ i ∈ ([136,140,144,148,152,156,160,164] : List (BitVec 64)),
      MemReadable s (rspOf s + i) 4)
    (allocated : ∀ i < 32, (t.external[destination + BitVec.ofNat 64 i]?).isSome)
    (state : SHA256.HashStateAt s (stackPtr s + 136) hash)
    (h : (serializeEffect next destination s).Holds s t) :
    (⟨destination.toNat, 32⟩ : MemoryRegion).HasBytes
      t.external (SHA256.serializeHash hash) := by
  have readable : ∀ j < 8, MemReadable s
      (stackPtr s + 136 + BitVec.ofNat 64 (4 * j)) 4 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero]
    all_goals first
      | exact sourceReadable 136 (by decide)
      | exact sourceReadable 140 (by decide)
      | exact sourceReadable 144 (by decide)
      | exact sourceReadable 148 (by decide)
      | exact sourceReadable 152 (by decide)
      | exact sourceReadable 156 (by decide)
      | exact sourceReadable 160 (by decide)
      | exact sourceReadable 164 (by decide)
  have values : ∀ j < 8,
      memLoad s.external (stackPtr s + 136 + BitVec.ofNat 64 (4 * j)) 32 = hash[j]!.toBitVec := by
    intro j hj
    exact SHA256.memLoad32_of_loadBytes4 (readable j hj).mem (state.2 j hj)
  have stores := h.writes
  simp only [serializeEffect, Write.AllHold, Operand.read] at stores
  have words : ∀ j < 8, memLoad t.external
      (destination + BitVec.ofNat 64 (4 * j)) 32 = bswap32 hash[j]!.toBitVec := by
    intro j hj
    rw [← values j hj]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have word := stores.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 0) 32 =
        bswap32 (memLoad s.external (stackPtr s + 136) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 4) 32 =
        bswap32 (memLoad s.external (stackPtr s + 140) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 8) 32 =
        bswap32 (memLoad s.external (stackPtr s + 144) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 12) 32 =
        bswap32 (memLoad s.external (stackPtr s + 148) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 16) 32 =
        bswap32 (memLoad s.external (stackPtr s + 152) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 20) 32 =
        bswap32 (memLoad s.external (stackPtr s + 156) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      change memLoad t.external (destination + 24) 32 =
        bswap32 (memLoad s.external (stackPtr s + 160) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word
    · have word := stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      change memLoad t.external (destination + 28) 32 =
        bswap32 (memLoad s.external (stackPtr s + 164) 32) at word
      simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using word

  have bytes := SHA256.bigEndian_bytes allocated words
  refine ⟨by simp only [MemoryRegion.HasLength, SHA256.serializeHash_size, state.1], ?_⟩
  intro i
  have hi : i.val < 32 := by
    simpa only [SHA256.serializeHash_size, state.1] using i.isLt
  change t.external[BitVec.ofNat 64 ((destination).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    SHA256.serializeHash_getElem]
  exact bytes i.val hi

theorem output {s t : RamState} {hash : Array UInt32}
    (pre : DigestPre s)
    (state : SHA256.HashStateAt s (stackPtr s + 136) hash)
    (h : (effect s).Holds s t) :
    (⟨(stackPtr s + 8).toNat, 32⟩ : MemoryRegion).HasBytes
      t.external (SHA256.serializeHash hash) := by

  have allocated : ∀ i < 32, (t.external[stackPtr s + 8 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have writable : Common.Instructions.CrossPageStore.Writable s
        (stackPtr s + 8 + BitVec.ofNat 64 (4 * (i / 4))) 4 := by
      have hj : i / 4 < 8 := by omega
      rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 ∨
        i / 4 = 4 ∨ i / 4 = 5 ∨ i / 4 = 6 ∨ i / 4 = 7) with
        hj | hj | hj | hj | hj | hj | hj | hj
      all_goals simp only [hj, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero]
      all_goals first
        | exact pre.writable 8 (by decide)
        | exact pre.writable 12 (by decide)
        | exact pre.writable 16 (by decide)
        | exact pre.writable 20 (by decide)
        | exact pre.writable 24 (by decide)
        | exact pre.writable 28 (by decide)
        | exact pre.writable 32 (by decide)
        | exact pre.writable 36 (by decide)
    have byte := (writable.of_holds h).mem (i % 4) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * (i / 4) + i % 4 = i by omega] at byte
    exact byte
  exact serializeEffect_output pre.readable allocated state h

end P256.Proofs.HMAC.Finalize.Digest
