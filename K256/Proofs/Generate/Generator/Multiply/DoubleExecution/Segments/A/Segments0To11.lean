import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment0 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880 b_l11d880_1 := by
  replay_segment using code_l11d880 from 53 to 89
    registers [4 => ⟨64, sp⟩] slots 27
    normalize [w1, w27, w28, w40, w41, w43, w44, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312,
      w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment1 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_1 b_l11d880_2 := by
  replay_segment using code_l11d880_1 from 89 to 128
    registers [4 => ⟨64, sp⟩, 59 => ⟨64, w4 p yy zz sp⟩, 87 => ⟨64, w8 p yy zz sp⟩] slots 27
    normalize [w1, w27, w28, w45, w46, w50, w51, w57, w58, w59, w60, w80, w121, w128, w133, w157, w160,
      w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment2 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_2 b_l11d880_3 := by
  replay_segment using code_l11d880_2 from 128 to 172
    registers [4 => ⟨64, sp⟩, 5 => ⟨64, 0x1000003d10⟩, 73 => ⟨64, w41 p yy zz sp⟩, 83 => ⟨64, w43 p yy zz
      sp⟩, 85 => ⟨64, w44 p yy zz sp⟩, 92 => ⟨64, w46 p yy zz sp⟩, 94 => ⟨64, w45 p yy zz sp⟩, 105 => ⟨64,
      w51 p yy zz sp⟩, 107 => ⟨64, w50 p yy zz sp⟩, 112 => ⟨64, w11 p yy zz sp⟩, 120 => ⟨64, w57 p yy zz
      sp⟩, 122 => ⟨64, w58 p yy zz sp⟩, 126 => ⟨64, w60 p yy zz sp⟩] slots 27
    normalize [w1, w27, w28, w59, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75,
      w76, w78, w79, w80, w81, w82, w83, w85, w86, w121, w128, w133, w157, w160, w257, w284, w312, w322,
      w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment3 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_3 b_l11d880_4 := by
  replay_segment using code_l11d880_3 from 172 to 212
    registers [4 => ⟨64, sp⟩, 78 => ⟨64, w9 p yy zz sp⟩, 96 => ⟨64, w5 p yy zz sp⟩, 149 => ⟨64, w75 p yy zz
      sp⟩, 152 => ⟨64, w79 p yy zz sp⟩, 154 => ⟨64, w81 p yy zz sp⟩, 169 => ⟨64, w86 p yy zz sp⟩, 170 =>
      ⟨64, w85 p yy zz sp⟩] slots 29
    normalize [w1, w27, w28, w59, w80, w90, w91, w92, w93, w94, w95, w96, w121, w128, w133, w157, w160,
      w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment4 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_4 b_l11d880_5 := by
  replay_segment using code_l11d880_4 from 212 to 259
    registers [4 => ⟨64, sp⟩, 158 => ⟨64, w2 p yy zz sp⟩, 184 => ⟨64, w91 p yy zz sp⟩, 186 => ⟨64, w90 p yy
      zz sp⟩, 188 => ⟨64, w92 p yy zz sp⟩, 195 => ⟨64, w94 p yy zz sp⟩, 197 => ⟨64, w93 p yy zz sp⟩, 199 =>
      ⟨64, w7 p yy zz sp⟩, 206 => ⟨64, w95 p yy zz sp⟩, 208 => ⟨64, w96 p yy zz sp⟩, 210 => ⟨64, w81 p yy zz
      sp⟩] slots 32
    normalize [w1, w27, w28, w59, w80, w97, w98, w99, w100, w101, w102, w103, w104, w105, w106, w107, w108,
      w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w119, w120, w121, w122, w123, w124, w125,
      w128, w133, w157, w160, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment5 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_5 b_l11d880_6 := by
  replay_segment using code_l11d880_5 from 259 to 300
    registers [4 => ⟨64, sp⟩, 167 => ⟨64, w3 p yy zz sp⟩, 174 => ⟨64, w9 p yy zz sp⟩, 179 => ⟨64, w4 p yy zz
      sp⟩, 244 => ⟨64, w119 p yy zz sp⟩, 247 => ⟨64, w123 p yy zz sp⟩, 257 => ⟨64, w11 p yy zz sp⟩] slots 29
    normalize [w1, w27, w28, w59, w80, w121, w126, w127, w128, w129, w130, w131, w132, w133, w134, w135,
      w136, w157, w160, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment6 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_6 b_l11d880_7 := by
  replay_segment using code_l11d880_6 from 300 to 346
    registers [4 => ⟨64, sp⟩, 262 => ⟨64, w127 p yy zz sp⟩, 277 => ⟨64, w131 p yy zz sp⟩, 279 => ⟨64, w130 p
      yy zz sp⟩, 281 => ⟨64, w132 p yy zz sp⟩, 283 => ⟨64, w134 p yy zz sp⟩, 292 => ⟨64, w136 p yy zz sp⟩,
      294 => ⟨64, w135 p yy zz sp⟩, 298 => ⟨64, w8 p yy zz sp⟩] slots 31
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w137, w138, w139, w140, w141, w142, w143, w144,
      w145, w146, w147, w148, w149, w150, w151, w152, w153, w154, w155, w156, w157, w158, w159, w160, w161,
      w162, w163, w164, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment7 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_7 b_l11d880_8 := by
  replay_segment using code_l11d880_7 from 346 to 388
    registers [4 => ⟨64, sp⟩, 199 => ⟨64, w7 p yy zz sp⟩, 255 => ⟨64, w124 p yy zz sp⟩, 270 => ⟨64, w10 p yy
      zz sp⟩, 287 => ⟨64, w5 p yy zz sp⟩, 296 => ⟨64, w8 p yy zz sp⟩, 338 => ⟨64, w161 p yy zz sp⟩, 341 =>
      Value.ofBool (addSpec (w162 p yy zz sp) (w125 p yy zz sp)).2.CF, 343 => ⟨64, w163 p yy zz sp⟩] slots
      29
    normalize [w1, w6, w27, w28, w40, w41, w43, w44, w45, w46, w50, w51, w57, w58, w59, w60, w61, w62, w63,
      w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w76, w78, w79, w80, w81, w82, w83, w85, w86,
      w90, w91, w92, w93, w94, w95, w96, w97, w98, w99, w100, w101, w102, w103, w104, w105, w106, w107,
      w108, w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w120, w121, w122, w123, w125, w127,
      w128, w129, w131, w132, w133, w134, w136, w138, w139, w143, w147, w151, w156, w157, w158, w159, w160,
      w162, w164, w165, w166, w167, w168, w169, w170, w171, w172, w173, w174, w175, w257, w284, w312, w322,
      w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment8 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_8 b_l11d880_9 := by
  replay_segment using code_l11d880_8 from 388 to 436
    registers [4 => ⟨64, sp⟩, 300 => ⟨64, w6 p yy zz sp⟩, 325 => ⟨64, w155 p yy zz sp⟩, 360 => ⟨64, w169 p
      yy zz sp⟩, 362 => ⟨64, w170 p yy zz sp⟩, 373 => ⟨64, w172 p yy zz sp⟩, 375 => ⟨64, w171 p yy zz sp⟩,
      377 => ⟨64, w173 p yy zz sp⟩, 384 => ⟨64, w175 p yy zz sp⟩, 386 => ⟨64, w174 p yy zz sp⟩] slots 30
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w176, w177, w178, w179, w180, w181,
      w182, w183, w184, w185, w186, w187, w188, w189, w190, w191, w192, w193, w194, w195, w196, w197, w198,
      w199, w200, w201, w202, w203, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment9 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_9 b_l11d880_10 := by
  replay_segment using code_l11d880_9 from 436 to 479
    registers [4 => ⟨64, sp⟩, 270 => ⟨64, w10 p yy zz sp⟩, 364 => ⟨64, w11 p yy zz sp⟩, 368 => ⟨64, w4 p yy
      zz sp⟩, 388 => ⟨64, w9 p yy zz sp⟩, 429 => ⟨64, w201 p yy zz sp⟩, 431 => ⟨64, w202 p yy zz sp⟩, 432 =>
      Value.ofBool (addSpec (w198 p yy zz sp) (w173 p yy zz sp)).2.CF, 434 => ⟨64, w202 p yy zz sp⟩] slots
      28
    normalize [w1, w6, w27, w28, w40, w41, w43, w44, w45, w46, w50, w51, w57, w58, w59, w60, w61, w62, w63,
      w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w76, w78, w79, w80, w81, w82, w83, w85, w86,
      w90, w91, w92, w93, w94, w95, w96, w97, w98, w99, w100, w101, w102, w103, w104, w105, w106, w107,
      w108, w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w120, w121, w122, w123, w124, w125,
      w126, w127, w128, w129, w130, w131, w132, w133, w134, w135, w136, w137, w138, w139, w140, w141, w142,
      w143, w144, w145, w146, w147, w148, w149, w150, w151, w152, w153, w154, w155, w156, w157, w158, w159,
      w160, w161, w162, w164, w165, w166, w168, w170, w172, w173, w175, w177, w178, w182, w186, w191, w193,
      w194, w198, w203, w204, w205, w206, w207, w208, w209, w210, w211, w212, w213, w214, w257, w284, w312,
      w322, w334, w336, w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment10 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (_rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_10 b_l11d880_11 := by
  replay_segment using code_l11d880_10 from 479 to 527
    registers [300 => ⟨64, w6 p yy zz sp⟩, 410 => ⟨64, w190 p yy zz sp⟩, 444 => ⟨64, w206 p yy zz sp⟩, 446
      => ⟨64, w207 p yy zz sp⟩, 453 => ⟨64, w208 p yy zz sp⟩, 455 => ⟨64, w209 p yy zz sp⟩, 462 => ⟨64, w211
      p yy zz sp⟩, 464 => ⟨64, w210 p yy zz sp⟩, 466 => ⟨64, w212 p yy zz sp⟩, 473 => ⟨64, w214 p yy zz sp⟩,
      475 => ⟨64, w213 p yy zz sp⟩, 477 => ⟨64, w10 p yy zz sp⟩] slots 26
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w215, w216, w217, w218, w219, w220,
      w221, w222, w223, w224, w225, w226, w227, w228, w229, w230, w231, w232, w233, w234, w235, w236, w237,
      w238, w239, w240, w241, w242, w243, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666,
      w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment11 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_11 b_l11d880_12 := by
  replay_segment using code_l11d880_11 from 527 to 569
    registers [4 => ⟨64, sp⟩, 489 => ⟨64, w221 p yy zz sp⟩, 492 => ⟨64, w224 p yy zz sp⟩, 522 => ⟨64, w240 p
      yy zz sp⟩, 525 => ⟨64, w243 p yy zz sp⟩] slots 26
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w244, w245, w246, w247, w248, w249,
      w250, w251, w252, w253, w254, w255, w256, w257, w258, w259, w260, w284, w312, w322, w334, w336, w364,
      w373, w607, w615, w666, w1266, w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
