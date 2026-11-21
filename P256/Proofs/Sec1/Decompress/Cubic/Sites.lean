import P256.Proofs.Sec1.Decompress.Cubic.Support

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def squareSite : FieldCall.BinaryCallSite 2592 408 0x113890 280 :=
  { codeOffset := 0xfe0a
    disp := 0x3a81
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x13890 (by decide)
    layout := ⟨416, 408, 328, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 288
    rightAbove := by decide
    rightEnd := by decide
    rightApart := .inr (by decide) }

def cubeSite : FieldCall.BinaryCallSite 2592 408 0x113890 280 :=
  { codeOffset := 0xfe20
    disp := 0x3a6b
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x13890 (by decide)
    layout := ⟨416, 328, 112, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 288
    rightAbove := by decide
    rightEnd := by decide
    rightApart := .inl (by decide) }

def mulASite : FieldCall.BinaryCallSite 2592 408 0x113890 280 :=
  { codeOffset := 0xfe62
    disp := 0x3a29
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x13890 (by decide)
    layout := ⟨416, 408, 328, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 288
    rightAbove := by decide
    rightEnd := by decide
    rightApart := .inr (by decide) }

def addASite : FieldCall.BinaryCallSite 2592 408 0x1137c0 16 :=
  { codeOffset := 0xfe78
    disp := 0x3943
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
    layout := ⟨416, 112, 216, by decide, by decide, by decide, by decide,
      by decide, by decide, .inr (by decide)⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 328
    rightAbove := by decide
    rightEnd := by decide
    rightApart := .inl (by decide) }

def addBSite : FieldCall.BinaryCallSite 2592 408 0x1137c0 16 :=
  { codeOffset := 0xfec9
    disp := 0x38f2
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
    layout := ⟨416, 216, 80, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 408
    rightAbove := by decide
    rightEnd := by decide
    rightApart := .inl (by decide) }

end P256.Proofs.Sec1.Decompress.Cubic
