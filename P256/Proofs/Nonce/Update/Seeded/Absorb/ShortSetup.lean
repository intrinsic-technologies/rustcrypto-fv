import P256.Proofs.Nonce.Update.Absorb.Prefix.Head

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.ShortSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def bytes : List UInt8 := [0x41, 0x89, 0xfe, 0x4c, 0x1, 0xe7, 0x48, 0x89, 0xda]

def effect (s : RamState) : Effect :=
  { rip := 0x10a769
    writes := [⟨(.reg 14 : Operand 64), ((Operand.reg 7 : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 7 : Operand 64).read s + (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 7 : Operand 64).read s) ((Operand.reg 12 : Operand 64).read s)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a760 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa760 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a760) (codeRange 0x10a760 bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (movR32R32Effect 0x10a760 3 14 7) from mov_r32_r32_rex_effect_step 0x10a760 0x41 0xfe (by simp [RexNoWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa763 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x10a763 7 12) from add_r64_r64_effect_step 0x10a763 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a760 bytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa766 (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a766 2 3) from mov_r64_r64_effect_step 0x10a766 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a760 bytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa769 (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Seeded.Absorb.ShortSetup
