import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.B.From42
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.B.From56
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.B.From70

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxHeartbeats 2000000 in
theorem segmentsB {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_42 b_l11d880_83 := by
  refine BodySegment.trans (segment42 rsp rbp) ?_
  refine BodySegment.trans (segment43 rsp rbp) ?_
  refine BodySegment.trans (segment44 rsp rbp) ?_
  refine BodySegment.trans (segment45 rsp rbp) ?_
  refine BodySegment.trans (segment46 rsp rbp) ?_
  refine BodySegment.trans (segment47 rsp rbp) ?_
  refine BodySegment.trans (segment48 rsp rbp) ?_
  refine BodySegment.trans (segment49 rsp rbp) ?_
  refine BodySegment.trans (segment50 rsp rbp) ?_
  refine BodySegment.trans (segment51 rsp rbp) ?_
  refine BodySegment.trans (segment52 rsp rbp) ?_
  refine BodySegment.trans (segment53 rsp rbp) ?_
  refine BodySegment.trans (segment54 rsp rbp) ?_
  refine BodySegment.trans (segment55 rsp rbp) ?_
  refine BodySegment.trans (segment56 rsp rbp) ?_
  refine BodySegment.trans (segment57 rsp rbp) ?_
  refine BodySegment.trans (segment58 rsp rbp) ?_
  refine BodySegment.trans (segment59 rsp rbp) ?_
  refine BodySegment.trans (segment60 rsp rbp) ?_
  refine BodySegment.trans (segment61 rsp rbp) ?_
  refine BodySegment.trans (segment62 rsp rbp) ?_
  refine BodySegment.trans (segment63 rsp rbp) ?_
  refine BodySegment.trans (segment64 rsp rbp) ?_
  refine BodySegment.trans (segment65 rsp rbp) ?_
  refine BodySegment.trans (segment66 rsp rbp) ?_
  refine BodySegment.trans (segment67 rsp rbp) ?_
  refine BodySegment.trans (segment68 rsp rbp) ?_
  refine BodySegment.trans (segment69 rsp rbp) ?_
  refine BodySegment.trans (segment70 rsp rbp) ?_
  refine BodySegment.trans (segment71 rsp rbp) ?_
  refine BodySegment.trans (segment72 rsp rbp) ?_
  refine BodySegment.trans (segment73 rsp rbp) ?_
  refine BodySegment.trans (segment74 rsp rbp) ?_
  refine BodySegment.trans (segment75 rsp rbp) ?_
  refine BodySegment.trans (segment76 rsp rbp) ?_
  refine BodySegment.trans (segment77 rsp rbp) ?_
  refine BodySegment.trans (segment78 rsp rbp) ?_
  refine BodySegment.trans (segment79 rsp rbp) ?_
  refine BodySegment.trans (segment80 rsp rbp) ?_
  refine BodySegment.trans (segment81 rsp rbp) ?_
  exact segment82 rsp rbp

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
