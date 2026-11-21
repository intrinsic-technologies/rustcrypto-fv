import P256.Proofs.Program.FieldCall.Binary

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Proofs.Program

def squareYSite : FieldCall.BinaryCallSite 3360 760 0x113890 280 where
  codeOffset := 0x10a41
  disp := 0x2e4a
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨768, 744, 184, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 312
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def squareXSite : FieldCall.BinaryCallSite 3360 760 0x113890 280 where
  codeOffset := 0x10a8d
  disp := 0x2dfe
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨768, 744, 384, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 280
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def cubeXSite : FieldCall.BinaryCallSite 3360 760 0x113890 280 where
  codeOffset := 0x10aa3
  disp := 0x2de8
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨768, 384, 480, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 280
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def linearXSite : FieldCall.BinaryCallSite 3360 760 0x113890 280 where
  codeOffset := 0x10aeb
  disp := 0x2da0
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨768, 744, 384, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 280
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def addLinearSite : FieldCall.BinaryCallSite 3360 760 0x1137c0 16 where
  codeOffset := 0x10b01
  disp := 0x2cba
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨768, 480, 416, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 384
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def addConstantSite : FieldCall.BinaryCallSite 3360 760 0x1137c0 16 where
  codeOffset := 0x10b55
  disp := 0x2c66
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨768, 416, 480, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 744
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
