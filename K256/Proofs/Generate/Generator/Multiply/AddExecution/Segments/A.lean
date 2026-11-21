import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.A.From0
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.A.From14
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.A.From28

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open X86.UserProcess K256.Proofs.Generate.LIR K256.Proofs.Common.Point

theorem segmentsA {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410 b_l10a410_43 :=
  BodySegment.trans
    (segments0To13 inc s r)
    (BodySegment.trans
      (segments14To27 inc s r)
      (segments28To42 inc s r))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
