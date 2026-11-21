import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Common

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field (AdvanceTriple)

def outerBytesEffect (s : RamState) : Effect :=
  let sp := (Operand.reg 4 : Operand 64).read s
  let load (off : BitVec 64) := memLoad s.external (sp+off) 8
  { rip := 0x10b27d
    writes := [⟨(Operand.reg 0 : Operand 64), (load 18).setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), (load 29).setWidth 64⟩,
      ⟨(Operand.mem (sp+14) : Operand 8), load 33⟩,
      ⟨(Operand.mem (sp+33) : Operand 8), load 14⟩,
      ⟨(Operand.mem (sp+15) : Operand 8), load 32⟩,
      ⟨(Operand.mem (sp+32) : Operand 8), load 15⟩,
      ⟨(Operand.mem (sp+16) : Operand 8), load 31⟩,
      ⟨(Operand.mem (sp+31) : Operand 8), load 16⟩,
      ⟨(Operand.mem (sp+17) : Operand 8), load 30⟩,
      ⟨(Operand.mem (sp+30) : Operand 8), load 17⟩,
      ⟨(Operand.mem (sp+18) : Operand 8), load 29⟩,
      ⟨(Operand.mem (sp+29) : Operand 8), load 18⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem outerBytes_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s 0x10b223) (codeRange 0x10b1cf reverseBytes)
      (Effect.post outerBytesEffect) := by
  advance_begin (movzx_r32_m8_effect_step 0x10b223 0 (.sib 4 none 0 (.d8 14)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 84 5
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (stackPtr s+14) 1
    exact (hP.slot 14 1 (by decide) (by decide)).toMemReadable
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xb228 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x10b228 1 (.sib 4 none 0 (.d8 33)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 89 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb22d (by decide))⟩
    x86_norm
    exact (hP.slot 33 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b22d 1 (by decide) (.sib 4 none 0 (.d8 14)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 94 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb231 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 14 (by decide) (by decide)
    · x86_norm
      exact hP.code 14 1 94 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 14 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b231 0 (by decide) (.sib 4 none 0 (.d8 33)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 98 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb235 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 33 (by decide) (by decide)
    · x86_norm
      exact hP.code 33 1 98 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 33 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b235 0 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 102 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb23a (by decide))⟩
    x86_norm
    exact (hP.slot 15 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b23a 1 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 107 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb23f (by decide))⟩
    x86_norm
    exact (hP.slot 32 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b23f 1 (by decide) (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 112 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb243 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 15 (by decide) (by decide)
    · x86_norm
      exact hP.code 15 1 112 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 15 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b243 0 (by decide) (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 116 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb247 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 32 (by decide) (by decide)
    · x86_norm
      exact hP.code 32 1 116 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 32 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b247 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 120 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb24c (by decide))⟩
    x86_norm
    exact (hP.slot 16 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b24c 1 (.sib 4 none 0 (.d8 31)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 125 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb251 (by decide))⟩
    x86_norm
    exact (hP.slot 31 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b251 1 (by decide) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 130 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb255 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 16 (by decide) (by decide)
    · x86_norm
      exact hP.code 16 1 130 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 16 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b255 0 (by decide) (.sib 4 none 0 (.d8 31)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 134 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb259 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 31 (by decide) (by decide)
    · x86_norm
      exact hP.code 31 1 134 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 31 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b259 0 (.sib 4 none 0 (.d8 17)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 138 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb25e (by decide))⟩
    x86_norm
    exact (hP.slot 17 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b25e 1 (.sib 4 none 0 (.d8 30)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 143 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb263 (by decide))⟩
    x86_norm
    exact (hP.slot 30 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b263 1 (by decide) (.sib 4 none 0 (.d8 17)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 148 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb267 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 17 (by decide) (by decide)
    · x86_norm
      exact hP.code 17 1 148 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 17 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b267 0 (by decide) (.sib 4 none 0 (.d8 30)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 152 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb26b (by decide))⟩
    · x86_norm
      exact hP.byte_writable 30 (by decide) (by decide)
    · x86_norm
      exact hP.code 30 1 152 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 30 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b26b 0 (.sib 4 none 0 (.d8 18)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 156 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb270 (by decide))⟩
    x86_norm
    exact (hP.slot 18 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b270 1 (.sib 4 none 0 (.d8 29)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 161 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb275 (by decide))⟩
    x86_norm
    exact (hP.slot 29 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b275 1 (by decide) (.sib 4 none 0 (.d8 18)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 166 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb279 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 18 (by decide) (by decide)
    · x86_norm
      exact hP.code 18 1 166 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 18 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b279 0 (by decide) (.sib 4 none 0 (.d8 29)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 170 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb27d (by decide))⟩
    · x86_norm
      exact hP.byte_writable 29 (by decide) (by decide)
    · x86_norm
      exact hP.code 29 1 170 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 29 1 0 264 (by decide) (by decide) (by decide)
  advance_finish [outerBytesEffect, BitVec.setWidth_setWidth]

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
