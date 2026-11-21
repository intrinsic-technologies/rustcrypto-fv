import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec.Program.Routines Prelude X86Proofs
open P256.Proofs.Program P256.Proofs.Program.FieldCall

def inverseSelectSite : BinaryCallSite 4584 2280 0x114380 128 where
  codeOffset := 0xcfd3
  disp := 0x73a8
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2288,1912,152,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1848
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def xMultiplySite : BinaryCallSite 4584 2280 0x113890 280 where
  codeOffset := 0xd01a
  disp := 0x6871
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨2288,2272,952,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 152
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def yMultiplySite : BinaryCallSite 4584 2280 0x113890 280 where
  codeOffset := 0xd059
  disp := 0x6832
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨2288,2272,1880,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 152
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def xSelectSite : BinaryCallSite 4584 2280 0x114380 128 where
  codeOffset := 0xd0d3
  disp := 0x72a8
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2288,952,2176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1752
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def ySelectSite : BinaryCallSite 4584 2280 0x114380 128 where
  codeOffset := 0xd0f3
  disp := 0x7288
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2288,920,2144,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1720
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
