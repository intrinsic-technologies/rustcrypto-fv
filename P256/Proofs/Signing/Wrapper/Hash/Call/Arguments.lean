import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Common.Instructions

structure ArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x102a19

def argumentsBytes : List UInt8 :=
  [0x31,0xed,0x48,0x8d,0x7c,0x24,0x40,0x48,0x8d,0xb4,0x24,0x70,0x01,0,0,
   0x48,0x89,0xe2,0xb9,0x20,0,0,0,0x41,0xb8,1,0,0,0,0x45,0x31,0xc9]

def argumentsEffect (s : RamState) : Effect :=
  { rip := 0x102a39
    writes := [⟨(.reg 5 : Operand 64), 0⟩, ⟨(.reg 7 : Operand 64), rspOf s + 64⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 368⟩, ⟨(.reg 2 : Operand 64), rspOf s⟩,
      ⟨(.reg 1 : Operand 64), 32⟩, ⟨(.reg 8 : Operand 64), 1⟩,
      ⟨(.reg 9 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem arguments_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102a19 argumentsBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2a19 argumentsBytes
    (by decide) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem arguments_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArgumentsPre (codeRange 0x102a19 argumentsBytes)
      (Effect.post argumentsEffect) := by
  advance_begin (StepEffect.forgetFlags (h := xor_r32_r32_effect_step 0x102a19 0xed rfl))
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x2a1b (by decide))
  advance_then (lea_r64_effect_step 0x102a1b 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 2 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a20 (by decide))⟩
  advance_then (lea_r64_effect_step 0x102a20 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 7 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a28 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x102a28 0x48 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 15 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a2b (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x102a2b 0xb9 (by decide) 32)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 18 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a30 (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x102a30 0x41 0xb8
    (by simp [RexNoWPrefix]) (by decide) 1)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 23 6
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a36 (by decide))⟩
  advance_then (xor_r32_r32_rex_effect_step 0x102a36 0x45 0xc9 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102a19 argumentsBytes 29 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2a39 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect]
    all_goals simp [gprNumber, rexB, rexR, modrmRm, modrmReg]
  · intro i; cases i <;> x86_norm [argumentsEffect]
    all_goals simp [gprNumber, rexB, rexR, modrmRm, modrmReg]
  · x86_norm [argumentsEffect]

end P256.Proofs.Signing.Wrapper.Hash.Call
