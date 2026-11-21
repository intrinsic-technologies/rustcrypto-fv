import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Instructions.And
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field P256.Proofs.Common.Instructions

def bytes : List UInt8 :=
  [0x48,0x89,0xe8,0x48,0xb9,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x83,0xe5,0x3f,0x49,0x1,0xc6]

def fullLength (s : RamState) : BitVec 64 :=
  (Operand.reg 5 : Operand 64).read s &&& 0x7fffffffffffffc0

def tailLength (s : RamState) : BitVec 64 :=
  ((Operand.reg 5 : Operand 32).read s &&& 63).setWidth 64

def effect (s : RamState) : Effect :=
  { rip := 0x10d6e4
    writes := [⟨(.reg 0 : Operand 64), fullLength s⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 5 : Operand 64), tailLength s⟩,
      ⟨(.reg 14 : Operand 64), (Operand.reg 14 : Operand 64).read s + fullLength s⟩]
    flags := some (.ofStatusFlags
      (addSpec ((Operand.reg 14 : Operand 64).read s) (fullLength s)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d6ce bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd6ce bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d6ce)
      (codeRange 0x10d6ce bytes) (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10d6ce 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd6d1 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10d6d1 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x10d6ce bytes 3 10
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6db (by decide))⟩
  advance_then (and_r64_r64_effect_step 0x10d6db 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d6ce bytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6de (by decide))⟩
  advance_then (and_r32_imm8_effect_step 0x10d6de 0xe5 63 rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d6ce bytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6e1 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10d6e1 0x49 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d6ce bytes 19 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd6e4 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect, fullLength, tailLength]
  · x86_norm [effect, fullLength, tailLength]
    repeat constructor
  · intro i; cases i <;> x86_norm [effect, fullLength, tailLength] <;> rfl
  · x86_norm [effect, fullLength, tailLength]

end P256.Proofs.Verifying.Message.Hash.Long.Tail.Prefix
