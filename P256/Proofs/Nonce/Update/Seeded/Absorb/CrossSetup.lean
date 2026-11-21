import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.CrossSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def bytes : List UInt8 := [0x48, 0x8d, 0x1c, 0x16, 0x4c, 0x1, 0xe7]
def effect (s : RamState) : Effect :=
  { rip := 0x10a7bd
    writes := [⟨(.reg 3 : Operand 64), (.reg 6 : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (.reg 7 : Operand 64).read s + (.reg 12 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec ((.reg 7 : Operand 64).read s) ((.reg 12 : Operand 64).read s)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a7b6 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa7b6 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a7b6) (codeRange 0x10a7b6 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a7b6 0x48 (by simp [RexWPrefix]) 3 (.sib 6 (some 2) 0 .none) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa7ba (by decide))
  advance_then (add_r64_r64_effect_step 0x10a7ba 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a7b6 bytes 4 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7bd (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl,rfl⟩
  · intro i; cases i <;> x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero] <;> rfl
  · x86_norm [effect, BitVec.add_zero, BitVec.shiftLeft_zero]

end P256.Proofs.Nonce.Update.Seeded.Absorb.CrossSetup
