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

def prepareNegArgs0Bytes : List UInt8 := [0x4c,0x8d,0xbc,0x24,0xf8,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x70,0x4c,0x89,0xff]

def prepareNegArgs0Effect (s : RamState) : Effect :=
  { rip := 0x10487c
    writes := [⟨(Operand.reg 15 : Operand 64), (s.regValue .rsp) + 248⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 112⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 248⟩] }

set_option maxHeartbeats 800000 in
theorem prepareNegArgs0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10486c)
      (codeRange 0x10486c prepareNegArgs0Bytes) (Effect.post prepareNegArgs0Effect) := by
  advance_begin (lea_r64_effect_step 0x10486c 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4874 (by decide))
  advance_then (lea_r64_effect_step 0x104874 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10486c prepareNegArgs0Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4879 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104879 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10486c prepareNegArgs0Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x487c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareNegArgs0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareNegArgs0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareNegArgs0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareNegArgs0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
