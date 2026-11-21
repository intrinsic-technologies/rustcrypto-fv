import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def registerBytes : List UInt8 := [0x48, 0x8b, 0x9c, 0x24, 0xd0, 0x1, 0, 0]

def registerEffect (s : RamState) : Effect :=
  { rip := 0x10da55
    writes := [⟨(.reg 3 : Operand 64), memLoad s.external (stackPtr s + 464) 64⟩] }

theorem registers_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10da4d ∧
      MemReadable s (stackPtr s + 464) 8)
      (codeRange 0x10da4d registerBytes) (Effect.post registerEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10da4d 0x48
    (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.1, h.2⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xda55 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [registerEffect, stackPtr]
  · x86_norm [registerEffect, stackPtr]
    rfl
  · intro i
    cases i <;> x86_norm [registerEffect, stackPtr]
  · x86_norm [registerEffect, stackPtr]

end P256.Proofs.Verifying.Core
