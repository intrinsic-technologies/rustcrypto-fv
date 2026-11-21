import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.FieldCall

def xSite : BinaryCallSite 3464 2056 0x113890 280 where
  codeOffset := 0x3ed
  disp := 0x1349e
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨2064, 1040, 1808, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 176
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def ySite : BinaryCallSite 3464 2056 0x113890 280 where
  codeOffset := 0x442
  disp := 0x13449
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨2064, 1040, 2008, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 176
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end P256.Proofs.Ecdh.Normalize.Coordinates
