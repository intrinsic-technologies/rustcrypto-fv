import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Setup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def bytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0xb0,0,0,0,0x48,0x89,0xea]

def effect (s : RamState) : Effect :=
  { rip := 0x10278d
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 176⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rbp⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102782 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2782 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x102782)
      (codeRange 0x102782 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x102782 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x278a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10278a 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102782 bytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x278d (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Setup
