import P256.Proofs.Generate.Sampler.Setup
import P256.Proofs.Common.Der.Decode.Header.Control
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Nop.Triple
import P256.Proofs.Common.Refine.Lemma.Norm

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.SignatureFromDer.Parser.ReadSlice

def availableBytes : List UInt8 :=
  [0x49,0x83,0xfd,0x20,0x72,0x58,0x48,0x83,0xc5,0x20,0x66,0x90]

def availableEffect (s : RamState) : Effect :=
  { rip := 0x100ca0
    writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 32⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 5 : Operand 64).read s) 32).2) }

theorem available_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100c94 availableBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xc94 _ (by decide) (by decide +kernel)

theorem available_run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s => s.RIP = 0x100c94 ∧ 32 ≤ ((Operand.reg 13 : Operand 64).read s).toNat)
      (codeRange 0x100c94 availableBytes) availableEffect := by
  have next (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  advance_begin (cmp_r64_imm8_effect_step 0x100c94 0x49 0xfd 32 (by simp [RexWPrefix]) rfl rfl)
  case next => intro _ _; exact next 0xc98 (by decide)
  advance_then (P256.Proofs.Common.Der.Decode.Header.jcc_rel8_not_taken_effect_step 0x100c98 2 88)
  case sub => exact codeRange_slice_subset 0x100c94 availableBytes 4 2
  case mid =>
    intro s t hp hh ho
    refine ⟨⟨hh.rip,?_⟩,Effect.Avoids.of_noMem (by simp [nopEffect,Effect.components,Component.Covers]) _,
      next 0xc9a (by decide)⟩
    have carry := hh.flag .CF
    simp only [Effect.flag] at carry
    change (StatusFlags.ofRFLAGS t.RFLAGS).CF =
      (cmpSpec ((Operand.reg 13#5 : Operand 64).read s) 32#64).CF at carry
    change (StatusFlags.ofRFLAGS t.RFLAGS).CF = false
    rw [carry,P256.Proofs.Refine.cmpSpec_CF,decide_eq_false_iff_not]
    change ¬ ((Operand.reg 13#5 : Operand 64).read s).toNat < 32
    omega
  advance_then (add_r64_imm8_effect_step 0x100c9a 0x48 0xc5 32 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100c94 availableBytes 6 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      next 0xc9e (by decide)⟩
  advance_then (nop_66_effect_step 0x100c9e)
  case sub => exact codeRange_slice_subset 0x100c94 availableBytes 10 2
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      next 0xca0 (by decide)⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [availableEffect]
  · x86_norm [availableEffect]
    rfl
  · intro flag; cases flag <;> x86_norm [availableEffect] <;> rfl
  · x86_norm [availableEffect]

end P256.Proofs.Generate.Sampler
