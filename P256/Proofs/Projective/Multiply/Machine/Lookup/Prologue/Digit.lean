import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Shift
import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Xor
import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Sub
import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Setup
import P256.Proofs.Projective.Multiply.Machine.Lookup.Digit

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions

attribute [local x86_compose] P256.Proofs.Common.Instructions.sarFlags

structure DigitPre (s : RamState) : Prop where
  rip : s.RIP = 0x1044d3
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 12) 4
  apart : RangeApart (stackPtr s + 12) 4 0x1044d3 26

def digitBytes : List UInt8 :=
  [76, 141, 180, 36, 144, 0, 0, 0, 137, 84, 36, 12, 137, 208, 192, 248, 7, 65, 137, 215, 65, 48, 199, 65, 40, 199]

def digitEffect (s : RamState) : Effect :=
  let d := (s.regValue .rdx).setWidth 32 |>.setWidth 64
  let mask := (d.setWidth 8).sshiftRight 7
  let a := mergeGPR 8 mask d
  let b := mergeGPR 8 ((d.setWidth 8) ^^^ (a.setWidth 8)) d
  let result := subSpec (b.setWidth 8) (a.setWidth 8)
  { rip := 0x1044ed
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 144⟩,
      ⟨(Operand.mem (stackPtr s + 12) : Operand 32), (s.regValue .rdx).setWidth 32⟩,
      ⟨(Operand.reg 0 : Operand 64), a⟩,
      ⟨(Operand.reg 15 : Operand 64), mergeGPR 8 result.1 b⟩]
    flags := some (.ofStatusFlags result.2) }

set_option maxHeartbeats 1000000 in
theorem digit_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DigitPre (codeRange 0x1044d3 digitBytes) (Effect.post digitEffect) := by
  advance_begin (lea_r64_effect_step 0x1044d3 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x44db (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x1044db 2
    (.sib 4 none 0 (.d8 12)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (8 + j) (by omega)
      change stackPtr s + 12 + BitVec.ofNat 64 i = _ at he
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x44df (by decide))
  advance_then (mov_r32_r32_effect_step 0x1044df 0xd0 rfl)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 12 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44e1 (by decide))⟩
  advance_then (sar_al_seven_effect_step 0x1044e1)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44e4 (by decide))⟩
  advance_then (mov_r32_r32_rex_effect_step 0x1044e4 0x41 0xd7 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44e7 (by decide))⟩
  advance_then (xor_r8_r8_rex_effect_step 0x1044e7 0x41 0xc7 (by simp [RexPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44ea (by decide))⟩
  advance_then (sub_r8_r8_rex_effect_step 0x1044ea 0x41 0xc7 (by simp [RexPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044d3 digitBytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44ed (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [digitEffect, subSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [digitEffect, subSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [digitEffect, subSpec]
    all_goals rfl
  · x86_norm [digitEffect, subSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization
