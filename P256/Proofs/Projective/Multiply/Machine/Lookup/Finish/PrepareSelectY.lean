import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareSelectY0Bytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x4c,0x89,0xfa,0x89,0xe9]

def prepareSelectY0Effect (s : RamState) : Effect :=
  { rip := 0x104921
    writes := [⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 2 : Operand 64), s.regValue .r15⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareSelectY0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10490f)
      (codeRange 0x10490f prepareSelectY0Bytes) (Effect.post prepareSelectY0Effect) := by
  advance_begin (lea_r64_effect_step 0x10490f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4917 (by decide))
  advance_then (lea_r64_effect_step 0x104917 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10490f prepareSelectY0Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x491c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10491c 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10490f prepareSelectY0Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x491f (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10491f 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10490f prepareSelectY0Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4921 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareSelectY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSelectY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareSelectY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSelectY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
