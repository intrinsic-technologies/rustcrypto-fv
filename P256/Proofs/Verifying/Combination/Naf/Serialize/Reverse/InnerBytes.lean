import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Common

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field (AdvanceTriple)

def innerBytesEffect (s : RamState) : Effect :=
  let sp := (Operand.reg 4 : Operand 64).read s
  let load (off : BitVec 64) := memLoad s.external (sp+off) 8
  { rip := 0x10b2d7
    writes := [⟨(Operand.reg 0 : Operand 64), (load 23).setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), (load 24).setWidth 64⟩,
      ⟨(Operand.mem (sp+19) : Operand 8), load 28⟩,
      ⟨(Operand.mem (sp+28) : Operand 8), load 19⟩,
      ⟨(Operand.mem (sp+20) : Operand 8), load 27⟩,
      ⟨(Operand.mem (sp+27) : Operand 8), load 20⟩,
      ⟨(Operand.mem (sp+21) : Operand 8), load 26⟩,
      ⟨(Operand.mem (sp+26) : Operand 8), load 21⟩,
      ⟨(Operand.mem (sp+22) : Operand 8), load 25⟩,
      ⟨(Operand.mem (sp+25) : Operand 8), load 22⟩,
      ⟨(Operand.mem (sp+23) : Operand 8), load 24⟩,
      ⟨(Operand.mem (sp+24) : Operand 8), load 23⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem innerBytes_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s 0x10b27d) (codeRange 0x10b1cf reverseBytes)
      (Effect.post innerBytesEffect) := by
  advance_begin (movzx_r32_m8_effect_step 0x10b27d 0 (.sib 4 none 0 (.d8 19)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 174 5
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (stackPtr s+19) 1
    exact (hP.slot 19 1 (by decide) (by decide)).toMemReadable
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xb282 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x10b282 1 (.sib 4 none 0 (.d8 28)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 179 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb287 (by decide))⟩
    x86_norm
    exact (hP.slot 28 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b287 1 (by decide) (.sib 4 none 0 (.d8 19)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 184 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb28b (by decide))⟩
    · x86_norm
      exact hP.byte_writable 19 (by decide) (by decide)
    · x86_norm
      exact hP.code 19 1 184 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 19 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b28b 0 (by decide) (.sib 4 none 0 (.d8 28)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 188 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb28f (by decide))⟩
    · x86_norm
      exact hP.byte_writable 28 (by decide) (by decide)
    · x86_norm
      exact hP.code 28 1 188 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 28 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b28f 0 (.sib 4 none 0 (.d8 20)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 192 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb294 (by decide))⟩
    x86_norm
    exact (hP.slot 20 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b294 1 (.sib 4 none 0 (.d8 27)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 197 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb299 (by decide))⟩
    x86_norm
    exact (hP.slot 27 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b299 1 (by decide) (.sib 4 none 0 (.d8 20)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 202 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb29d (by decide))⟩
    · x86_norm
      exact hP.byte_writable 20 (by decide) (by decide)
    · x86_norm
      exact hP.code 20 1 202 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 20 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b29d 0 (by decide) (.sib 4 none 0 (.d8 27)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 206 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2a1 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 27 (by decide) (by decide)
    · x86_norm
      exact hP.code 27 1 206 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 27 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b2a1 0 (.sib 4 none 0 (.d8 21)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 210 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2a6 (by decide))⟩
    x86_norm
    exact (hP.slot 21 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b2a6 1 (.sib 4 none 0 (.d8 26)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 215 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2ab (by decide))⟩
    x86_norm
    exact (hP.slot 26 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2ab 1 (by decide) (.sib 4 none 0 (.d8 21)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 220 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2af (by decide))⟩
    · x86_norm
      exact hP.byte_writable 21 (by decide) (by decide)
    · x86_norm
      exact hP.code 21 1 220 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 21 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2af 0 (by decide) (.sib 4 none 0 (.d8 26)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 224 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2b3 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 26 (by decide) (by decide)
    · x86_norm
      exact hP.code 26 1 224 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 26 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b2b3 0 (.sib 4 none 0 (.d8 22)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 228 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2b8 (by decide))⟩
    x86_norm
    exact (hP.slot 22 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b2b8 1 (.sib 4 none 0 (.d8 25)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 233 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2bd (by decide))⟩
    x86_norm
    exact (hP.slot 25 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2bd 1 (by decide) (.sib 4 none 0 (.d8 22)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 238 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2c1 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 22 (by decide) (by decide)
    · x86_norm
      exact hP.code 22 1 238 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 22 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2c1 0 (by decide) (.sib 4 none 0 (.d8 25)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 242 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2c5 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 25 (by decide) (by decide)
    · x86_norm
      exact hP.code 25 1 242 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 25 1 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m8_effect_step 0x10b2c5 0 (.sib 4 none 0 (.d8 23)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 246 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2ca (by decide))⟩
    x86_norm
    exact (hP.slot 23 1 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m8_effect_step 0x10b2ca 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 251 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb2cf (by decide))⟩
    x86_norm
    exact (hP.slot 24 1 (by decide) (by decide)).toMemReadable
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2cf 1 (by decide) (.sib 4 none 0 (.d8 23)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 256 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2d3 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 23 (by decide) (by decide)
    · x86_norm
      exact hP.code 23 1 256 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 23 1 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m8_r8_legacy_effect_step 0x10b2d3 0 (by decide) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 260 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb2d7 (by decide))⟩
    · x86_norm
      exact hP.byte_writable 24 (by decide) (by decide)
    · x86_norm
      exact hP.code 24 1 260 4 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 24 1 0 264 (by decide) (by decide) (by decide)
  advance_finish [innerBytesEffect, BitVec.setWidth_setWidth]

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
