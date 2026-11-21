import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

structure RelocatePre (s : RamState) : Prop where
  rip : s.RIP = 0x110128
  readable : MemReadable s (stackPtr s + 240) 1

def relocateBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0xb4, 0x24, 0xf0, 0, 0, 0,
   0x48, 0x8d, 0x54, 0x24, 0x10, 0xb9, 0x0a, 0, 0, 0,
   0x48, 0x89, 0xd7, 0x4c, 0x89, 0xfe]

def relocateEffect (s : RamState) : Effect :=
  { rip := 0x110141
    writes := [⟨(.reg 14 : Operand 64), (memLoad s.external (stackPtr s + 240) 8).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 1 : Operand 64), 10⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r15⟩] }

set_option maxHeartbeats 800000 in
theorem relocate_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary RelocatePre (codeRange 0x110128 relocateBytes) relocateEffect := by
  unfold relocateBytes
  slice_run_begin (show StepEffect _ _ (movzxR32M8Effect 0x110128 9 14 (.sib 4 none 0 (.d32 240))) from
    movzx_r32_m8_rex_effect_step 0x110128 0x44 (by simp [RexNoWPrefix])
      6 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10131 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110131 2 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110131 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110128) 9 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10136 (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x110136 5 1 10) from
    mov_r32_imm32_effect_step 0x110136 0xb9 (by decide) 10)
  case sub => exact codeRange_mem_of_drop (p := 0x110128) 14 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1013b (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x11013b 7 2) from
    mov_r64_r64_effect_step 0x11013b 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110128) 19 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1013e (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x11013e 6 15) from
    mov_r64_r64_effect_step 0x11013e 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110128) 22 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10141 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [relocateEffect]
  · x86_norm [relocateEffect] <;> rfl
  · intro f; cases f <;> x86_norm [relocateEffect]
  · x86_norm [relocateEffect]

end P256.Proofs.Sec1.Affine.Compressed.Finish
