import P256.Proofs.Projective.Double.CrossTerms.Memory
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

def subtractionSite : BinaryCallSite 1016 728 0x1137e0 24 where
  codeOffset := 0x604e
  disp := 0xd78d
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨736, 688, 400, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def additionSite : BinaryCallSite 1016 728 0x1137c0 16 where
  codeOffset := 0x609a
  disp := 0xd721
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨736, 720, 144, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 432
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def y_productSite : BinaryCallSite 1016 728 0x113890 280 where
  codeOffset := 0x60e6
  disp := 0xd7a5
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨736, 144, 112, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def x_productSite : BinaryCallSite 1016 728 0x113890 280 where
  codeOffset := 0x60f9
  disp := 0xd792
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨736, 400, 208, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 176
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end Products
end P256.Proofs.Projective.Double
