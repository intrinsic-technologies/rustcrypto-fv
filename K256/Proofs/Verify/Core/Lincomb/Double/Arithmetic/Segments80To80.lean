import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment80 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_80 b_l110d64_81 := by
  replay_segment using code_l110d64_80 from 3464 to 3504
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3434 => ⟨64, w257 p yy zz sp⟩, 3438 => ⟨64, v2003 p yy zz sp⟩, 3444 => ⟨64,
      v2007 p yy zz sp⟩, 3450 => ⟨64, v2010 p yy zz sp⟩, 3456 => ⟨64, v2013 p yy zz sp⟩, 3460 => ⟨64, v1591
      p yy zz sp⟩, 3462 => ⟨64, v2016 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v2017, v2018, v2019, v2020, v2021, v2022, v2023, v2024, v2026, v2027, v2029, v2030,
      v2032, v2033]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
