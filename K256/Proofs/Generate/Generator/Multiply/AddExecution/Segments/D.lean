import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.D.Part1
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.D.Part2
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.D.Part3

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

theorem segmentsD {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_129 b_l10a410_171 := by
  exact BodySegment.trans (BodySegment.trans (@segmentsD1 code inc s r)
    (@segmentsD2 code inc s r)) (@segmentsD3 code inc s r)

end K256.Proofs.Generate.Generator.Multiply.AddReplay
