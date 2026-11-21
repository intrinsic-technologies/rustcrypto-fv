import P256.Proofs.Projective.Double.Products.Pre
import P256.Proofs.Projective.Double.Values
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

namespace Products

def x_productBytes : List UInt8 :=
  [72, 141, 188, 36, 8, 2, 0, 0, 76, 137, 230, 76, 137, 242]

def x_productEffect (s : RamState) : Effect :=
  { rip := 0x1060f9
    writes := [
      ⟨(.reg 7 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 520)⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

theorem x_product_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary (MovePre 0x1060eb [] [])
      (codeRange 0x1060eb x_productBytes) (Effect.post x_productEffect) := by
  advance_begin (lea_r64_effect_step 0x1060eb 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 520)) (by decide) rfl rfl)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x60f3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1060f3 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1060eb x_productBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60f6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1060f6 0x4c 0xf2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1060eb x_productBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60f9 (by decide))
  advance_finish [x_productEffect]


end Products
end P256.Proofs.Projective.Double
