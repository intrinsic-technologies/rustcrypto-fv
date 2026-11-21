import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixBytes : List UInt8 :=
  [0x48,0x89,0xfb,0x41,0xbe,0x1,0x0,0x0,0x0]

def prefixEffect (s : RamState) : Effect :=
  { rip := 0x10fa37
    writes := [⟨(.reg 3 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64), 1⟩] }

theorem prefix_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fa2e) (codeRange 0x10fa2e prefixBytes)
      (Effect.post prefixEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10fa2e 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfa31 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10fa31 0x41 0xbe (by simp [RexNoWPrefix]) (by decide +kernel) 1)
  case sub => exact codeRange_slice_subset 0x10fa2e prefixBytes 3 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfa37 (by decide))
  advance_finish [prefixEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
