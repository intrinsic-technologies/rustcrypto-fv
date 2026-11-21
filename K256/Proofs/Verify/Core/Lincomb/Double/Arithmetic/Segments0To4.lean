import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment0 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64 b_l110d64_1 := by
  replay_segment using code_l110d64 from 53 to 86
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩]
    normalize [w1, w28, w40, w41, w43, w44, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334,
      w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment1 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_1 b_l110d64_2 := by
  replay_segment using code_l110d64_1 from 86 to 125
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 80 => ⟨64, w4 p yy zz sp⟩, 83 => ⟨64, w8 p yy zz sp⟩]
    normalize [w1, w28, w45, w46, w50, w51, w57, w58, w59, w60, w80, w121, w128, w133, w157, w160, w257,
      w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment2 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_2 b_l110d64_3 := by
  replay_segment using code_l110d64_2 from 125 to 169
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 56 => ⟨64, w3 p yy zz sp⟩, 61 => ⟨64, w10 p yy zz sp⟩, 77 => ⟨64, w44 p yy zz
      sp⟩, 89 => ⟨64, w46 p yy zz sp⟩, 91 => ⟨64, w45 p yy zz sp⟩, 102 => ⟨64, w51 p yy zz sp⟩, 104 => ⟨64,
      w50 p yy zz sp⟩, 108 => ⟨64, w11 p yy zz sp⟩, 117 => ⟨64, w58 p yy zz sp⟩, 119 => ⟨64, w57 p yy zz
      sp⟩, 123 => ⟨64, w60 p yy zz sp⟩]
    normalize [w1, w28, w59, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76,
      w78, w79, w80, w81, w82, w83, w85, w86, w92, w121, w128, w133, w157, w160, w257, w284, w322, w334,
      w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment3 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_3 b_l110d64_4 := by
  replay_segment using code_l110d64_3 from 169 to 212
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 93 => ⟨64, w5 p yy zz sp⟩, 106 => ⟨64, w6 p yy zz sp⟩, 151 => ⟨64, w81 p yy zz
      sp⟩, 166 => ⟨64, w86 p yy zz sp⟩, 167 => ⟨64, w85 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w90, w91, w93, w94, w95, w96, w97, w98, w121, w128, w133, w157, w160,
      w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment4 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_4 b_l110d64_5 := by
  replay_segment using code_l110d64_4 from 212 to 256
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 153 => ⟨64, w92 p yy zz sp⟩, 157 => ⟨64, w2 p yy zz sp⟩, 170 => ⟨64, w86 p yy
      zz sp⟩, 181 => ⟨64, w90 p yy zz sp⟩, 183 => ⟨64, w91 p yy zz sp⟩, 190 => ⟨64, w93 p yy zz sp⟩, 192 =>
      ⟨64, w94 p yy zz sp⟩, 194 => ⟨64, w7 p yy zz sp⟩, 201 => ⟨64, w95 p yy zz sp⟩, 203 => ⟨64, w96 p yy zz
      sp⟩, 209 => ⟨64, w98 p yy zz sp⟩, 210 => ⟨64, w97 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w99, w100, w101, w102, w103, w104, w105, w106, w107, w108, w109, w110,
      w111, w112, w113, w114, w115, w116, w117, w118, w119, w120, w121, w122, w123, w124, w125, w128, w129,
      w132, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
