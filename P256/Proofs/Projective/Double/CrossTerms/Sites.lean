import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.FieldCall
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def mulXYSite : BinaryCallSite 1016 728 0x113890 280 where
  codeOffset := 0x5e1c
  disp := 0xda6f
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨736, 688, 656, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def mulXZSite : BinaryCallSite 1016 728 0x113890 280 where
  codeOffset := 0x5e8d
  disp := 0xd9fe
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨736, 688, 656, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def mulBZZSite : BinaryCallSite 1016 728 0x113890 280 where
  codeOffset := 0x5f24
  disp := 0xd967
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨736, 720, 656, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 688
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def differenceSite : BinaryCallSite 1016 728 0x1137e0 24 where
  codeOffset := 0x5f70
  disp := 0xd86b
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨736, 656, 464, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def tripleDifferenceSite : BinaryCallSite 1016 728 0x1137c0 16 where
  codeOffset := 0x5fcc
  disp := 0xd7ef
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨736, 688, 432, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end P256.Proofs.Projective.Double.CrossTerms
