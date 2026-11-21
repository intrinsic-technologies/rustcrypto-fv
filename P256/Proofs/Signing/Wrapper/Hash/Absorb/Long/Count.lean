import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.Instructions.And
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Count

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions

def bytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xf0,0x0,0x0,0x0,0x49,0xbf,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x49,0x21,0xef,0x41,0x89,0xec,0x41,0x83,0xe4,0x3f,0x49,0x1,0xf7,0x48,0xc1,0xed,0x6]

def effect (s : RamState) : Effect :=
  { rip := 0x102820
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 240⟩,
      ⟨(.reg 15 : Operand 64), (0x7fffffffffffffc0 &&& s.regValue .rbp) + s.regValue .rsi⟩,
      ⟨(.reg 12 : Operand 64), ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64⟩,
      ⟨(.reg 5 : Operand 64), s.regValue .rbp >>> 6⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x1027fd bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x27fd bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1027fd)
      (codeRange 0x1027fd bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x1027fd 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x2805 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x102805 0x49 0xbf (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x1027fd bytes 8 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [movR64Imm64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x280f (by decide))
  advance_then (StepEffect.forgetFlags (h := and_r64_r64_effect_step 0x10280f 0x49 0xef (by simp [RexWPrefix]) rfl))
  case sub => exact codeRange_slice_subset 0x1027fd bytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, andR64R64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2812 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x102812 0x41 0xec (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1027fd bytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [movR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2815 (by decide))
  advance_then (StepEffect.forgetFlags (h := and_r32_imm8_rex_effect_step 0x102815 0x41 0xe4 63 (by simp [RexNoWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x1027fd bytes 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, andR32Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2819 (by decide))
  advance_then (StepEffect.forgetFlags (h := add_r64_r64_effect_step 0x102819 0x49 0xf7 (by simp [RexWPrefix]) rfl))
  case sub => exact codeRange_slice_subset 0x1027fd bytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, addR64R64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x281c (by decide))
  advance_then (StepEffect.forgetFlags (h := shr_r64_imm8_effect_step 0x10281c 0x48 0xed 6 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x1027fd bytes 31 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, shrR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2820 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [effect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Count
