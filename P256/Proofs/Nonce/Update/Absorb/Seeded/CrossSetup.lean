import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.CrossSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def bytes : List UInt8 := [0x4d, 0x8d, 0x3c, 0x14, 0x4c, 0x8d, 0xac, 0x24, 0x98, 0x0, 0x0, 0x0, 0x4c, 0x1, 0xef, 0x4c, 0x89, 0xe6]

def effect (s : RamState) : Effect :=
  { rip := 0x10a2fd
    writes := [⟨(.reg 15 : Operand 64), (Operand.reg 12 : Operand 64).read s + (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), rspOf s + 152⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 7 : Operand 64).read s + (rspOf s + 152)⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 7 : Operand 64).read s) (rspOf s + 152)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a2eb bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa2eb bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a2eb) (codeRange 0x10a2eb bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a2eb 0x4d (by simp [RexWPrefix]) 7 (.sib 12 (some 2) 0 .none) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa2ef (by decide))
  advance_then (lea_r64_effect_step 0x10a2ef 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2eb bytes 4 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2f7 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10a2f7 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a2eb bytes 12 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2fa (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a2fa 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a2eb bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2fd (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl,rfl⟩
  · intro i; cases i <;> x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero] <;> rfl
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]

end P256.Proofs.Nonce.Update.Absorb.Seeded.CrossSetup
