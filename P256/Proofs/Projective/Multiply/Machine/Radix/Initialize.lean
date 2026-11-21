import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Load
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] movM8Imm8Effect

structure InitializePre (s : RamState) : Prop where
  rip : s.RIP = 0x10b728
  lastWritable : MemWritable s ((Operand.reg 4 : Operand 64).read s + 72) 1
  writable : ∀ i ∈ ([8,16,24,32,40,48,56,64] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ (i : BitVec 64) (n : Nat),
    (i,n) ∈ [(72,1),(8,8),(16,8),(24,8),(32,8),(40,8),(48,8),(56,8),(64,8)] →
    ∀ offset len : Nat, offset + len ≤ 118431 →
      RangeApart ((Operand.reg 4 : Operand 64).read s + i) n
        (Extracted.textAddress + BitVec.ofNat 64 offset) len

def initializeBytes : List UInt8 :=
  [0xc6, 0x44, 0x24, 0x48, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x7c, 0x24, 0x50]

def initializeEffect (s : RamState) : Effect :=
  { rip := 0x10b77a
    writes := [
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 80⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 72) : Operand 8), 0⟩ ] }

set_option maxHeartbeats 1000000 in
theorem initialize_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InitializePre (codeRange 0x10b728 initializeBytes)
      (Effect.post initializeEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10b728 (.sib 4 none 0 (.d8 72))
    (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip, h.lastWritable, h.codeApart 72 1 (by simp) 0xb728 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 72 1 (by simp) 0xb728 82 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xb72d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b72d 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 64))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 5 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 8 (by simp) 0xb72d 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb736 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b736 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 56))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 14 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 8 (by simp) 0xb736 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb73f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b73f 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 48))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 23 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 8 (by simp) 0xb73f 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb748 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b748 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 40))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 32 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 8 (by simp) 0xb748 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb751 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b751 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 32))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 41 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 8 (by simp) 0xb751 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb75a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b75a 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 24))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 50 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 8 (by simp) 0xb75a 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb763 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b763 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 16))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 59 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 8 (by simp) 0xb763 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb76c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10b76c 0x48
    (by unfold RexWPrefix; decide +kernel) (.sib 4 none 0 (.d8 8))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 68 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 8 (by simp) 0xb76c 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 8 (by simp) 0xb728 82 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb775 (by decide))
  advance_then (lea_r64_effect_step 0x10b775 0x48 (by unfold RexWPrefix; decide +kernel) 7
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10b728 initializeBytes 77 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb77a (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [initializeEffect]
  · x86_norm [initializeEffect]
  · intro i
    cases i <;> x86_norm [initializeEffect]
  · x86_norm [initializeEffect]

end P256.Proofs.Projective.Multiply.Machine.Radix
