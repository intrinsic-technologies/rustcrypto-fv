import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment5 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_5 b_l110d64_6 := by
  replay_segment using code_l110d64_5 from 256 to 298
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 172 => ⟨64, w9 p yy zz sp⟩, 176 => ⟨64, w4 p yy zz sp⟩, 247 => ⟨64, w129 p yy
      zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w126, w127, w128, w130, w131, w133, w134, w135, w136, w157, w160,
      w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment6 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_6 b_l110d64_7 := by
  replay_segment using code_l110d64_6 from 298 to 344
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 245 => ⟨64, w132 p yy zz sp⟩, 266 => ⟨64, w127 p yy zz sp⟩, 275 => ⟨64, w131 p
      yy zz sp⟩, 277 => ⟨64, w130 p yy zz sp⟩, 279 => ⟨64, w134 p yy zz sp⟩, 288 => ⟨64, w135 p yy zz sp⟩,
      290 => ⟨64, w136 p yy zz sp⟩, 294 => ⟨64, w8 p yy zz sp⟩, 296 => ⟨64, w6 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w137, w138, w139, w140, w141, w142, w143, w144, w145,
      w146, w147, w148, w149, w150, w151, w152, w153, w154, w155, w156, w157, w158, w159, w160, w161, w162,
      w163, w164, w165, w166, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment7 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_7 b_l110d64_8 := by
  replay_segment using code_l110d64_7 from 344 to 385
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 256 => ⟨64, w11 p yy zz sp⟩, 260 => ⟨64, w3 p yy zz sp⟩, 268 => ⟨64, w10 p yy
      zz sp⟩, 283 => ⟨64, w5 p yy zz sp⟩, 292 => ⟨64, w8 p yy zz sp⟩, 336 => ⟨64, w163 p yy zz sp⟩, 342 =>
      ⟨64, w166 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w167, w168, w169, w170, w171, w172, w173,
      w174, w175, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment8 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_8 b_l110d64_9 := by
  replay_segment using code_l110d64_8 from 385 to 432
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 296 => ⟨64, w6 p yy zz sp⟩, 321 => ⟨64, w155 p yy zz sp⟩, 361 => ⟨64, w169 p
      yy zz sp⟩, 363 => ⟨64, w170 p yy zz sp⟩, 372 => ⟨64, w171 p yy zz sp⟩, 374 => ⟨64, w172 p yy zz sp⟩,
      378 => ⟨64, w175 p yy zz sp⟩, 383 => ⟨64, w174 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w176, w177, w178, w179, w180, w181, w182,
      w183, w184, w185, w186, w187, w188, w189, w190, w191, w192, w193, w194, w195, w196, w197, w198, w199,
      w200, w201, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment9 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_9 b_l110d64_10 := by
  replay_segment using code_l110d64_9 from 432 to 475
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 256 => ⟨64, w11 p yy zz sp⟩, 354 => ⟨64, w7 p yy zz sp⟩, 367 => ⟨64, w4 p yy
      zz sp⟩, 381 => ⟨64, w5 p yy zz sp⟩, 387 => ⟨64, w9 p yy zz sp⟩, 427 => ⟨64, w198 p yy zz sp⟩, 430 =>
      ⟨64, w201 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w202, w203, w204, w205, w206, w207, w208,
      w209, w210, w211, w212, w213, w214, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580,
      BitVec.mul_one]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
