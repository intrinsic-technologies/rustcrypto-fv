import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field

def bytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x4c,0x89,0xfe,0x4c,0x89,0xe2]

def effect (s : RamState) : Effect :=
  { rip := 0x102846
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 176⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102838 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2838 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x102838)
      (codeRange 0x102838 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x102838 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x2840 (by decide))
  advance_then (mov_r64_r64_effect_step 0x102840 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102838 bytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2843 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x102843 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102838 bytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2846 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect, BitVec.add_zero]
  · x86_norm [effect, BitVec.add_zero]
    repeat constructor
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Setup
