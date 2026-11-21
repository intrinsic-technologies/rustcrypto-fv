import P256.Proofs.Generate.Sampler.Setup

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.SignatureFromDer.Parser.ReadSlice

def argumentBytes : List UInt8 := [0x4c,0x89,0xff,0x4c,0x89,0xe6]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x100cd5
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem arguments_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100ccf argumentBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xccf _ (by decide) (by decide +kernel)

theorem arguments_run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100ccf)
      (codeRange 0x100ccf argumentBytes) argumentEffect := by
  advance_begin (mov_r64_r64_effect_step 0x100ccf 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcd2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100cd2 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100ccf argumentBytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcd5 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [argumentEffect]
  · x86_norm [argumentEffect]
    exact ⟨rfl,rfl⟩
  · intro flag; cases flag <;> x86_norm [argumentEffect]
  · x86_norm [argumentEffect]

end P256.Proofs.Generate.Sampler
