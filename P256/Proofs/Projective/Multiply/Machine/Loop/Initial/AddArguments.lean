import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def addArgumentsBytes : List UInt8 :=
  [76, 137, 247, 76, 137, 230]

def addArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1032ea
    writes := [⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

theorem addArguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1032e4)
      (codeRange 0x1032e4 addArgumentsBytes) (Effect.post addArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1032e4 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x32e7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1032e7 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032e4 addArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32ea (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [addArgumentsEffect]
  · x86_norm [addArgumentsEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [addArgumentsEffect]
  · x86_norm [addArgumentsEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
