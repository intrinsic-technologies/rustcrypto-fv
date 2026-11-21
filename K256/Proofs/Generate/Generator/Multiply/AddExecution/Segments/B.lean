import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.B.Tails43To53
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.B.Tails54To64
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.B.Tails65To75
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.B.Tails76To85

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

theorem segmentsB {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_43 b_l10a410_86 :=
  BodySegment.trans
    (BodySegment.trans (segments43To53 inc s r) (segments54To64 inc s r))
    (BodySegment.trans (segments65To75 inc s r) (segments76To85 inc s r))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
