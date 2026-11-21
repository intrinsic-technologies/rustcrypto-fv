import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.FieldCall

def xSite : BinaryCallSite 3352 1944 0x113890 280 where
  codeOffset := 0xe9f7
  disp := 0x4e94
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨1952, 1680, 912, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1712
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def ySite : BinaryCallSite 3352 1944 0x113890 280 where
  codeOffset := 0xea40
  disp := 0x4e4b
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨1952, 1680, 1912, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1712
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end P256.Proofs.PublicPoint.Normalize.Coordinates
