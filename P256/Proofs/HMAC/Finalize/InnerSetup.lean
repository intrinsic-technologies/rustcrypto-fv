import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
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

namespace P256.Proofs.HMAC.Finalize.InnerSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Instructions

attribute [local x86_compose] movM8Imm8Effect

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x100f9b
  writable : MemWritable s (rspOf s + 239) 1
  codeApart : RangeApart (rspOf s + 239) 1 0x100f9b 25

def bytes : List UInt8 :=
  [0xc6,0x84,0x24,0xef,0,0,0,0,0x49,0x83,0xc7,0x40,
    0x48,0x8d,0x7c,0x24,0x48,0xb9,0x0d,0,0,0,0x4c,0x89,0xfe]

def effect (s : RamState) : Effect :=
  { rip := 0x100fb4
    writes := [⟨(.mem (rspOf s + 239) : Operand 8), 0⟩,
      ⟨(.reg 15 : Operand 64), (.reg 15 : Operand 64).read s + 64⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 72⟩,
      ⟨(.reg 1 : Operand 64), 13⟩,
      ⟨(.reg 6 : Operand 64), (.reg 15 : Operand 64).read s + 64⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100f9b bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xf9b bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x100f9b bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x100f9b
    (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      exact h.writable
    · x86_norm
      intro i hi j hj
      exact h.codeApart i hi j (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xfa3 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    add_r64_imm8_effect_step 0x100fa3 0x49 0xc7 64 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x100f9b bytes 8 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfa7 (by decide))
  advance_then (lea_r64_effect_step 0x100fa7 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f9b bytes 12 5
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfac (by decide))
  advance_then (mov_r32_imm32_effect_step 0x100fac 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x100f9b bytes 17 5
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb1 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100fb1 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100f9b bytes 22 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb4 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.HMAC.Finalize.InnerSetup
