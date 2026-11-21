import P256.Proofs.Verifying.Combination.Loop.MultiLength

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def addSetupBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x48,0x4c,0x89,0xfe]

def addSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f2b0
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r15⟩] }

theorem addSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f2a8)
      (codeRange 0x10f2a8 addSetupBytes) (Effect.post addSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f2a8 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf2ad (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f2ad 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f2a8 addSetupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2b0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [addSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [addSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [addSetupEffect]
  · x86_norm [addSetupEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Loop.Multi
