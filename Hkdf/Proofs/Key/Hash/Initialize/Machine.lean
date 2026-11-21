import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import Hkdf.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Initialize

open Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Machine

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x11638e
  writable : ∀ slot ∈ ([(320,8),(312,8),(304,8),(296,8),(295,1),(328,8)] : List (Nat × Nat)),
    MemWritable s (rspOf s + BitVec.ofNat 64 slot.1) slot.2
  codeApart : ∀ slot ∈ ([(320,8),(312,8),(304,8),(296,8),(295,1),(328,8)] : List (Nat × Nat)),
    ∀ offset len : Nat, 0x11638e ≤ offset → offset + len ≤ 0x11640e →
    RangeApart (rspOf s + BitVec.ofNat 64 slot.1) slot.2 (BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0xb8, 0xab, 0xd9,
   0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01,
   0x00, 0x00, 0x48, 0xb8, 0x7f, 0x52, 0x0e, 0x51, 0x8c, 0x68, 0x05, 0x9b,
   0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0xb8, 0x72, 0xf3,
   0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01,
   0x00, 0x00, 0x48, 0xb8, 0x67, 0xe6, 0x09, 0x6a, 0x85, 0xae, 0x67, 0xbb,
   0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0xc6, 0x84, 0x24, 0x27,
   0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xd0, 0x48, 0xc1, 0xe8, 0x06, 0x49,
   0xbe, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x49, 0x21, 0xd6,
   0x83, 0xe2, 0x3f, 0x49, 0x01, 0xf6, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01,
   0x00, 0x00, 0x49, 0x89, 0xd7, 0x48, 0x89, 0xc2]

def effect (s : RamState) : Effect :=
  { rip := 0x11640e
    writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 296⟩,
      ⟨(.reg 0 : Operand 64), s.regValue .rdx >>> 6⟩,
      ⟨(.mem (rspOf s + 320) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (rspOf s + 312) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (rspOf s + 304) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (rspOf s + 296) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (rspOf s + 295) : Operand 8), 0⟩,
      ⟨(.reg 14 : Operand 64), (0x7fffffffffffffc0 &&& s.regValue .rdx) + s.regValue .rsi⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rdx >>> 6⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), s.regValue .rdx >>> 6⟩,
      ⟨(.reg 15 : Operand 64), ((s.regValue .rdx).setWidth 32 &&& 63).setWidth 64⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11638e bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1638e bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x11638e bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x11638e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x16396 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x116396 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case sub => exact codeRange_slice_subset 0x11638e bytes 8 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163a0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1163a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (320,8) (by simp)
    · x86_norm
      exact hP.codeApart (320,8) (by simp) 0x1163a0 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (320,8) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163a8 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1163a8 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x11638e bytes 26 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163b2 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1163b2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (312,8) (by simp)
    · x86_norm
      exact hP.codeApart (312,8) (by simp) 0x1163b2 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (312,8) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163ba (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1163ba 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x11638e bytes 44 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163c4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1163c4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 54 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (304,8) (by simp)
    · x86_norm
      exact hP.codeApart (304,8) (by simp) 0x1163c4 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (304,8) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163cc (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1163cc 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x11638e bytes 62 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163d6 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1163d6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (296,8) (by simp)
    · x86_norm
      exact hP.codeApart (296,8) (by simp) 0x1163d6 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (296,8) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163de (by decide))
  advance_then (mov_m8_imm8_effect_step 0x1163de (.sib 4 none 0 (.d32 295)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11638e bytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (295,1) (by simp)
    · x86_norm
      exact hP.codeApart (295,1) (by simp) 0x1163de 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (295,1) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163e6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1163e6 0x48 0xd0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 88 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163e9 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1163e9 0x48 0xe8 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 91 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163ed (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1163ed 0x49 0xbe (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x11638e bytes 95 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163f7 (by decide))
  advance_then (and_r64_r64_effect_step 0x1163f7 0x49 0xd6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 105 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163fa (by decide))
  advance_then (and_r32_imm8_effect_step 0x1163fa 0xe2 63 rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 108 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x163fd (by decide))
  advance_then (add_r64_r64_effect_step 0x1163fd 0x49 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 111 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16400 (by decide))
  advance_then (mov_m64_r64_effect_step 0x116400 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 114 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable (328,8) (by simp)
    · x86_norm
      exact hP.codeApart (328,8) (by simp) 0x116400 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart (328,8) (by simp) 0x11638e 128 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16408 (by decide))
  advance_then (mov_r64_r64_effect_step 0x116408 0x49 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 122 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1640b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11640b 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11638e bytes 125 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1640e (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i
    cases i <;> exact Or.inl rfl
  · x86_norm [effect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

end Hkdf.Proofs.Key.Hash.Initialize
