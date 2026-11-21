import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short.Setup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

def bytes : List UInt8 :=
  [0x48,0x8d,0x3c,0x1c,0x48,0x81,0xc7,0xd8,0x1,0x0,0x0,0x4c,0x89,0xf6,0x4c,0x89,0xfa]

def effect (s : RamState) : Effect :=
  { rip := 0x10d621
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + (Operand.reg 3 : Operand 64).read s + 472⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d610 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd610 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d610)
      (codeRange 0x10d610 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10d610 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 (some 3) 0 .none) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd614 (by decide))
  advance_then (StepEffect.forgetFlags (h := add_r64_imm32_effect_step 0x10d614 0x48 0xc7 472
    (by constructor <;> decide) (by decide) (by decide)))
  case sub => exact codeRange_slice_subset 0x10d610 bytes 4 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Effect.forgetFlags, addR64Imm32Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd61b (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d61b 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d610 bytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd61e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d61e 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d610 bytes 14 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd621 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [effect, BitVec.shiftLeft_zero, BitVec.add_zero]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [effect, BitVec.shiftLeft_zero, BitVec.add_zero]

end P256.Proofs.Verifying.Message.Hash.Short.Setup
