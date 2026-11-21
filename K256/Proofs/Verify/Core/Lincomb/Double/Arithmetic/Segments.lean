import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments0To4
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments5To9
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments10To14
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments15To19
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments20To24
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments25To29
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments30To34
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments35To39
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments40To44
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments45To49
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments50To54
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments55To59
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments60To64
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments65To69
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments70To74
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments75To79
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments80To80

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Proofs.Verify.LIR CFG Common.Point Common.Field Lift

theorem segments {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64,sp⟩) : Segment a p yy zz sp b_l110d64 b_l110d64_81 := by
  refine Segment.trans (segment0 rsp) ?_
  refine Segment.trans (segment1 rsp) ?_
  refine Segment.trans (segment2 rsp) ?_
  refine Segment.trans (segment3 rsp) ?_
  refine Segment.trans (segment4 rsp) ?_
  refine Segment.trans (segment5 rsp) ?_
  refine Segment.trans (segment6 rsp) ?_
  refine Segment.trans (segment7 rsp) ?_
  refine Segment.trans (segment8 rsp) ?_
  refine Segment.trans (segment9 rsp) ?_
  refine Segment.trans (segment10 rsp) ?_
  refine Segment.trans (segment11 rsp) ?_
  refine Segment.trans (segment12 rsp) ?_
  refine Segment.trans (segment13 rsp) ?_
  refine Segment.trans (segment14 rsp) ?_
  refine Segment.trans (segment15 rsp) ?_
  refine Segment.trans (segment16 rsp) ?_
  refine Segment.trans (segment17 rsp) ?_
  refine Segment.trans (segment18 rsp) ?_
  refine Segment.trans (segment19 rsp) ?_
  refine Segment.trans (segment20 rsp) ?_
  refine Segment.trans (segment21 rsp) ?_
  refine Segment.trans (segment22 rsp) ?_
  refine Segment.trans (segment23 rsp) ?_
  refine Segment.trans (segment24 rsp) ?_
  refine Segment.trans (segment25 rsp) ?_
  refine Segment.trans (segment26 rsp) ?_
  refine Segment.trans (segment27 rsp) ?_
  refine Segment.trans (segment28 rsp) ?_
  refine Segment.trans (segment29 rsp) ?_
  refine Segment.trans (segment30 rsp) ?_
  refine Segment.trans (segment31 rsp) ?_
  refine Segment.trans (segment32 rsp) ?_
  refine Segment.trans (segment33 rsp) ?_
  refine Segment.trans (segment34 rsp) ?_
  refine Segment.trans (segment35 rsp) ?_
  refine Segment.trans (segment36 rsp) ?_
  refine Segment.trans (segment37 rsp) ?_
  refine Segment.trans (segment38 rsp) ?_
  refine Segment.trans (segment39 rsp) ?_
  refine Segment.trans (segment40 rsp) ?_
  refine Segment.trans (segment41 rsp) ?_
  refine Segment.trans (segment42 rsp) ?_
  refine Segment.trans (segment43 rsp) ?_
  refine Segment.trans (segment44 rsp) ?_
  refine Segment.trans (segment45 rsp) ?_
  refine Segment.trans (segment46 rsp) ?_
  refine Segment.trans (segment47 rsp) ?_
  refine Segment.trans (segment48 rsp) ?_
  refine Segment.trans (segment49 rsp) ?_
  refine Segment.trans (segment50 rsp) ?_
  refine Segment.trans (segment51 rsp) ?_
  refine Segment.trans (segment52 rsp) ?_
  refine Segment.trans (segment53 rsp) ?_
  refine Segment.trans (segment54 rsp) ?_
  refine Segment.trans (segment55 rsp) ?_
  refine Segment.trans (segment56 rsp) ?_
  refine Segment.trans (segment57 rsp) ?_
  refine Segment.trans (segment58 rsp) ?_
  refine Segment.trans (segment59 rsp) ?_
  refine Segment.trans (segment60 rsp) ?_
  refine Segment.trans (segment61 rsp) ?_
  refine Segment.trans (segment62 rsp) ?_
  refine Segment.trans (segment63 rsp) ?_
  refine Segment.trans (segment64 rsp) ?_
  refine Segment.trans (segment65 rsp) ?_
  refine Segment.trans (segment66 rsp) ?_
  refine Segment.trans (segment67 rsp) ?_
  refine Segment.trans (segment68 rsp) ?_
  refine Segment.trans (segment69 rsp) ?_
  refine Segment.trans (segment70 rsp) ?_
  refine Segment.trans (segment71 rsp) ?_
  refine Segment.trans (segment72 rsp) ?_
  refine Segment.trans (segment73 rsp) ?_
  refine Segment.trans (segment74 rsp) ?_
  refine Segment.trans (segment75 rsp) ?_
  refine Segment.trans (segment76 rsp) ?_
  refine Segment.trans (segment77 rsp) ?_
  refine Segment.trans (segment78 rsp) ?_
  refine Segment.trans (segment79 rsp) ?_
  exact segment80 rsp

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
