import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentBytes : List UInt8 :=
  [0x48, 0x89, 0xf2, 0xbe, 4, 0, 0, 0, 0xb9, 4, 0, 0, 0]

def argumentEffect (pc : BitVec 64) (s : RamState) : Effect :=
  { rip := pc + 13
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), 4⟩, ⟨(.reg 1 : Operand 64), 4⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64)
    (outside : ∀ i ∈ ([3,8,13] : List Nat), pc + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = pc)
      (codeRange pc argumentBytes) (Effect.post (argumentEffect pc)) := by
  advance_begin (mov_r64_r64_effect_step pc 0x48 0xf2 (by simp [RexWPrefix]) rfl)
  case next =>
    intro _ _
    exact outside 3 (by simp)
  advance_then (mov_r32_imm32_effect_step (pc + 3) 0xbe (by decide +kernel) 4)
  try (case sub => exact codeRange_slice_subset pc argumentBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 8 (by simp)
  advance_then (mov_r32_imm32_effect_step (pc + 8) 0xb9 (by decide +kernel) 4)
  try (case sub => exact codeRange_slice_subset pc argumentBytes 8 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 13 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [argumentEffect]
  · x86_norm [argumentEffect]
    rfl
  · intro i
    cases i <;> x86_norm [argumentEffect]
  · x86_norm [argumentEffect]

end P256.Proofs.Generate.Zero
