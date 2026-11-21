import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.EnterTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def bytes : List UInt8 := [0x49, 0x89, 0xee, 0xeb, 0x3d]

def effect (s : RamState) : Effect :=
  { rip := 0x10a2c3, writes := [⟨(.reg 14 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a281 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa281 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a281) (codeRange 0x10a281 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10a281 0x49 0xee (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa284 (by decide))
  advance_then (jmp_rel8_effect_step 0x10a284 0x3d (by decide))
  case sub => exact codeRange_slice_subset 0x10a281 bytes 3 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2c3 (by decide))⟩
  advance_finish [effect] <;> rfl

end P256.Proofs.Nonce.Update.Absorb.Seeded.EnterTail
