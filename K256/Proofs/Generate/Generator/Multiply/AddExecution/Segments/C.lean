import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.C.Range86
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.C.Range97
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.C.Range108
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Segments.C.Range119

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

theorem segmentsC {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_86 b_l10a410_129 :=
  BodySegment.trans (BodySegment.trans (segments86To96 inc s r)
      (segments97To107 inc s r))
    (BodySegment.trans (segments108To118 inc s r)
      (segments119To128 inc s r))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
