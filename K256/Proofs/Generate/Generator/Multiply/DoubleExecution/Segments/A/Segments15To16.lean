import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

private theorem negationOffset_eq (p : PointWords) (yy zz : Limbs) (sp : Word) :
    w337 p yy zz sp = (0x3ffffffffffffc : Word) := by
  change (0x3ffffffffffffc : Word) * (1 : Word) = (0x3ffffffffffffc : Word)
  exact BitVec.mul_one _

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment15 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_15 b_l11d880_16 := by
  replay_segment using code_l11d880_15 from 681 to 720
    registers [4 => ⟨64, sp⟩, 617 => ⟨64, w286 p yy zz sp⟩, 632 => ⟨64, w295 p yy zz sp⟩, 666 => ⟨64, w319 p
      yy zz sp⟩] slots 28
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w327, w328,
      w329, w330, w331, w333, w334, w336, ↓negationOffset_eq, w338, w339, w340, w341, w342, w343, w344, w364, w373, w607,
      w615, w666, w1266, w1270, BitVec.shiftLeft_zero]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment16 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_16 b_l11d880_17 := by
  replay_segment using code_l11d880_16 from 720 to 759
    registers [4 => ⟨64, sp⟩, 642 => ⟨64, w304 p yy zz sp⟩, 654 => ⟨64, w314 p yy zz sp⟩, 697 => ⟨64, w334 p
      yy zz sp⟩, 714 => ⟨64, w344 p yy zz sp⟩, 716 => ⟨64, w344 p yy zz sp⟩, 718 => ⟨64, w59 p yy zz sp⟩]
      slots 29
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      ↓negationOffset_eq, w346, w348, w349, w350, w351, w352, w353, w354, w356, w357, w358, w360, w362, w364, w373, w607,
      w615, w666, w1266, w1270, BitVec.shiftLeft_zero]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
