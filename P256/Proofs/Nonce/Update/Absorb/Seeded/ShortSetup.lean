import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.ShortSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def bytes : List UInt8 := [0x89, 0xfb, 0x48, 0x8d, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x1, 0xc7, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xfa]

def effect (s : RamState) : Effect :=
  { rip := 0x10a2a3
    writes := [⟨(.reg 3 : Operand 64), ((Operand.reg 7 : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 0 : Operand 64), rspOf s + 152⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 7 : Operand 64).read s + (rspOf s + 152)⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 7 : Operand 64).read s) (rspOf s + 152)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a290 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa290 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a290) (codeRange 0x10a290 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_r32_effect_step 0x10a290 0xfb rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa292 (by decide))
  advance_then (lea_r64_effect_step 0x10a292 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a290 bytes 2 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa29a (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10a29a 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a290 bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa29d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a29d 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a290 bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2a0 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a2a0 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a290 bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2a3 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero] <;> rfl
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]

end P256.Proofs.Nonce.Update.Absorb.Seeded.ShortSetup
