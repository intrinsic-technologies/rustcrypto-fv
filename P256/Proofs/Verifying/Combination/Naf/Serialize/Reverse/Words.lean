import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Common

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field (AdvanceTriple)

def wordsEffect (s : RamState) : Effect :=
  let sp := (Operand.reg 4 : Operand 64).read s
  let load (off : BitVec 64) := memLoad s.external (sp+off) 16
  { rip := 0x10b223
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 ((load 12).rotateLeft 8) ((load 12).setWidth 64)⟩,
      ⟨(Operand.reg 1 : Operand 64), mergeGPR 16 ((load 34).rotateLeft 8) ((load 34).setWidth 64)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 16 ((load 38).rotateLeft 8) ((load 38).setWidth 64)⟩,
      ⟨(Operand.mem (sp+8) : Operand 16), (load 38).rotateLeft 8⟩,
      ⟨(Operand.mem (sp+38) : Operand 16), (load 8).rotateLeft 8⟩,
      ⟨(Operand.mem (sp+10) : Operand 16), (load 36).rotateLeft 8⟩,
      ⟨(Operand.mem (sp+36) : Operand 16), (load 10).rotateLeft 8⟩,
      ⟨(Operand.mem (sp+12) : Operand 16), (load 34).rotateLeft 8⟩,
      ⟨(Operand.mem (sp+34) : Operand 16), (load 12).rotateLeft 8⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem words_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s 0x10b1cf) (codeRange 0x10b1cf reverseBytes)
      (Effect.post wordsEffect) := by
  advance_begin (movzx_r32_m16_effect_step 0x10b1cf 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 0 5
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (stackPtr s+8) 2
    exact (hP.slot 8 2 (by decide) (by decide)).toMemReadable
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xb1d4 (by decide))
  advance_then (rol_r16_eight_effect_step 0x10b1d4 0xc0 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 5 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1d8 (by decide))⟩
  advance_then (movzx_r32_m16_effect_step 0x10b1d8 1 (.sib 4 none 0 (.d8 10)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1dd (by decide))⟩
    x86_norm
    exact (hP.slot 10 2 (by decide) (by decide)).toMemReadable
  advance_then (movzx_r32_m16_effect_step 0x10b1dd 2 (.sib 4 none 0 (.d8 38)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 14 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1e2 (by decide))⟩
    x86_norm
    exact (hP.slot 38 2 (by decide) (by decide)).toMemReadable
  advance_then (rol_r16_eight_effect_step 0x10b1e2 0xc2 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 19 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1e6 (by decide))⟩
  advance_then (mov_m16_r16_effect_step 0x10b1e6 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb1eb (by decide))⟩
    · x86_norm
      exact hP.slot 8 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 8 2 23 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 8 2 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m16_r16_effect_step 0x10b1eb 0 (.sib 4 none 0 (.d8 38)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb1f0 (by decide))⟩
    · x86_norm
      exact hP.slot 38 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 38 2 28 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 38 2 0 264 (by decide) (by decide) (by decide)
  advance_then (rol_r16_eight_effect_step 0x10b1f0 0xc1 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 33 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1f4 (by decide))⟩
  advance_then (movzx_r32_m16_effect_step 0x10b1f4 0 (.sib 4 none 0 (.d8 36)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 37 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1f9 (by decide))⟩
    x86_norm
    exact (hP.slot 36 2 (by decide) (by decide)).toMemReadable
  advance_then (rol_r16_eight_effect_step 0x10b1f9 0xc0 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 42 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb1fd (by decide))⟩
  advance_then (mov_m16_r16_effect_step 0x10b1fd 0 (.sib 4 none 0 (.d8 10)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 46 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb202 (by decide))⟩
    · x86_norm
      exact hP.slot 10 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 10 2 46 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 10 2 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m16_r16_effect_step 0x10b202 1 (.sib 4 none 0 (.d8 36)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 51 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb207 (by decide))⟩
    · x86_norm
      exact hP.slot 36 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 36 2 51 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 36 2 0 264 (by decide) (by decide) (by decide)
  advance_then (movzx_r32_m16_effect_step 0x10b207 0 (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 56 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb20c (by decide))⟩
    x86_norm
    exact (hP.slot 12 2 (by decide) (by decide)).toMemReadable
  advance_then (rol_r16_eight_effect_step 0x10b20c 0xc0 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 61 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb210 (by decide))⟩
  advance_then (movzx_r32_m16_effect_step 0x10b210 1 (.sib 4 none 0 (.d8 34)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 65 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb215 (by decide))⟩
    x86_norm
    exact (hP.slot 34 2 (by decide) (by decide)).toMemReadable
  advance_then (rol_r16_eight_effect_step 0x10b215 0xc1 rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 70 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [rolR16Effect, Effect.components, Write.component, Operand.component, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xb219 (by decide))⟩
  advance_then (mov_m16_r16_effect_step 0x10b219 1 (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb21e (by decide))⟩
    · x86_norm
      exact hP.slot 12 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 12 2 74 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 12 2 0 264 (by decide) (by decide) (by decide)
  advance_then (mov_m16_r16_effect_step 0x10b21e 0 (.sib 4 none 0 (.d8 34)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10b1cf reverseBytes 79 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xb223 (by decide))⟩
    · x86_norm
      exact hP.slot 34 2 (by decide) (by decide)
    · x86_norm
      exact hP.code 34 2 79 5 (by decide) (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.code 34 2 0 264 (by decide) (by decide) (by decide)
  advance_finish [wordsEffect, BitVec.setWidth_setWidth]

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
