import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments0To11
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments12To14
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments15To16
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments17To23
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments24To35
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A.Segments36To41

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open Common.Point Common.Field

private theorem range0 {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880 b_l11d880_12 := by
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment0 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment1 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment2 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment3 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment4 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment5 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment6 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment7 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment8 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment9 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment10 rsp rbp) ?_
  exact segment11 rsp rbp

private theorem range12 {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_12 b_l11d880_24 := by
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment12 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment13 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment14 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment15 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment16 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment17 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment18 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment19 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment20 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment21 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment22 rsp rbp) ?_
  exact segment23 rsp rbp

private theorem range24 {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_24 b_l11d880_36 := by
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment24 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment25 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment26 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment27 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment28 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment29 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment30 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment31 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment32 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment33 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment34 rsp rbp) ?_
  exact segment35 rsp rbp

private theorem range36 {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_36 b_l11d880_42 := by
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment36 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment37 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment38 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment39 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (segment40 rsp rbp) ?_
  exact segment41 rsp rbp

theorem segmentsA {a : Registers} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880 b_l11d880_42 := by
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (range0 rsp rbp) ?_
  refine @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (range12 rsp rbp) ?_
  exact @BodySegment.trans _ _ _ _ _ _ _ _ _ _ (range24 rsp rbp) (range36 rsp rbp)

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
