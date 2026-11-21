import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Projective.Double.Output.Copy

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Double.Output.YZCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def codeBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x0, 0x2, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0xf8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x84, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xf0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8]

private theorem reg_write_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem mem_write_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

theorem correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CopyPre 0x1063cc 4 488 8) (codeRange 0x1063cc codeBytes)
      (Effect.post (copyEffect 0x106400 4 488 8)) := by
  advance_begin (mov_r64_m64_effect_step 0x1063cc 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 512)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, by simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using h.readable 24 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x63d4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1063d4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 24 (by simp) 0x63d4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 24 (by simp) 0x63cc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63d9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1063d9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 504)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63e1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1063e1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 16 (by simp) 0x63e1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 16 (by simp) 0x63cc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63e6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1063e6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 488)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63ee (by decide))
  advance_then (mov_r64_m64_effect_step 0x1063ee 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 496)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63f6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1063f6 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 8 (by simp) 0x63f6 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 8 (by simp) 0x63cc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x63fb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1063fb 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1063cc codeBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.writable 0 (by simp)
    · x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 0 (by simp) 0x63fb 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa (config := {decide := true}) only [x86_compose, stackPtr, BitVec.add_assoc, Operand.read_reg64, Extracted.textAddress] using hP.codeApart 0 (by simp) 0x63cc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6400 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0, 8, 16, 24] : List (BitVec 64)))
      (hj : j ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
      memLoad (memStore mem (stackPtr s + (8 + i)) v)
        ((Operand.reg 4 : Operand 64).read s + (488 + j)) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + (488 + j)) 64 :=
    P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart _ _ _ _ 64 (copy_source_apart hP i hi j hj)
  have h2416 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h240 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h248 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h160 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h168 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  x86_norm [stackPtr, Operand.read_reg64] at h2416 h240 h248 h160 h168
  apply hH.weaken
  · x86_norm [copyEffect, Copy32.effect, stackPtr, Operand.read_reg64, reg_write_external, mem_write_external]
  · x86_norm [copyEffect, Copy32.effect, stackPtr, Operand.read_reg64, reg_write_external, mem_write_external, h2416, h240, h248, h160, h168]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect, Copy32.effect, stackPtr, Operand.read_reg64, reg_write_external, mem_write_external]
  · x86_norm [copyEffect, Copy32.effect, stackPtr, Operand.read_reg64, reg_write_external, mem_write_external]

end P256.Proofs.Projective.Double.Output.YZCopy
