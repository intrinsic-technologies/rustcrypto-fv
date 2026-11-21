import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def identitySetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x48, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x48, 0xc7, 0xc6, 0x40, 0x2e, 0x20, 0x0]

def identitySetupEffect (s : RamState) : Effect :=
  { rip := 0x10f12b
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), 0x202e40⟩] }

theorem identitySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f11a)
      (codeRange 0x10f11a identitySetupBytes) (Effect.post identitySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f11a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf11f (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10f11f 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10f11a identitySetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf124 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10f124 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202e40)
  case sub => exact codeRange_slice_subset 0x10f11a identitySetupBytes 10 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf12b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [identitySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [identitySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [identitySetupEffect]
  · x86_norm [identitySetupEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Loop.Multi
