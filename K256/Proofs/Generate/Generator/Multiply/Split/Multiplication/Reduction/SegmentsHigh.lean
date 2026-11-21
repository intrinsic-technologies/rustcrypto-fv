import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Layout

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

private theorem replayAddLow (x y : BitVec 64) :
    (addSpec x y).1 = x + y := rfl

private theorem replayAdcLow (c : Bool) (x y : BitVec 64) :
    (adcSpec c x y).1 = x + y + BitVec.ofNat 64 c.toNat := rfl

private theorem subNegTwo (x : BitVec 64) : x - 0xfffffffffffffffe = x + 2 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem widenByte (x : BitVec 8) :
    (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment5 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (_rsi : a[6] = ⟨64, fr.rsi⟩)
    (_constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (_lo : 129 ≤ fr.rsp.toNat) (_hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (_upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_5 b_l11b5ba_6 := by
  replay_segment using code_l11b5ba_5 from 283 to 329
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 140 => ⟨64, (v140 w)⟩, 184 => ⟨64, (v184 w)⟩, 203 => ⟨64, (v203 w)⟩, 206 => ⟨64, (v206 w)⟩, 271 => ⟨64, (v271 w)⟩, 275 => ⟨64, (v275 w)⟩, 277 => ⟨64, (v277 w)⟩, 278 => ⟨64, (v278 w)⟩, 280 => ⟨64, (v280 w)⟩, 281 => Value.ofBool (v281 w)]
    normalize [replayAdcLow, replayAddLow, v283, v285, v287, v288, v290, v292, v293, v295, v297, v299, v300, v302, v304, v305, v307, v309, v311, v313, v315, v316, v318, v320, v321, v323, v325, v327]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment6 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (_rsi : a[6] = ⟨64, fr.rsi⟩)
    (_constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_6 b_l11b5ba_7 := by
  replay_segment using code_l11b5ba_6 from 329 to 375
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 100 => ⟨64, (v100 w)⟩, 261 => ⟨64, (v261 w)⟩, 275 => ⟨64, (v275 w)⟩, 292 => ⟨64, (v292 w)⟩, 320 => ⟨64, (v320 w)⟩, 323 => ⟨64, (v323 w)⟩, 325 => ⟨64, (v325 w)⟩, 327 => ⟨64, (v327 w)⟩]
    normalize [replayAdcLow, replayAddLow, v329, v330, v332, v334, v336, v338, v339, v341, v342, v344, v346, v348, v349, v351, v353, v354, v356, v357, v359, v360, v362, v363, v365, v368, v371, v373]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment7 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (_rsi : a[6] = ⟨64, fr.rsi⟩)
    (_constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_7 b_l11b5ba_8 := by
  replay_segment using code_l11b5ba_7 from 375 to 412
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 222 => ⟨64, (v222 w)⟩, 356 => ⟨64, (v356 w)⟩, 373 => ⟨64, (v373 w)⟩]
    normalize [v375, v380, v382, v385, v387, v389, v391, v393, v395, v397, v399, v401, v403, v405, v407, v409]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment8 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (_rsi : a[6] = ⟨64, fr.rsi⟩)
    (_constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_8 b_l11b5ba_9 := by
  replay_segment using code_l11b5ba_8 from 412 to 451
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 236 => ⟨64, (v236 w)⟩, 304 => ⟨64, (v304 w)⟩, 359 => ⟨64, (v359 w)⟩, 362 => ⟨64, (v362 w)⟩]
    normalize [replayAddLow, subNegTwo, v412, v414, v416, v418, v420, v422, v424, v426, v428, v430, v432, v434, v436, v438, v440, v443, v445, v447, v449]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem segment9 {a : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : a[4] = ⟨64, fr.rsp - 120⟩) (_rsi : a[6] = ⟨64, fr.rsi⟩)
    (_constant : a[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) :
    Segment a fr w b_l11b5ba_9 barrier := by
  replay_segment using code_l11b5ba_9 from 451 to 483
    atoms (memoryAtoms fr w) unfold memoryAtoms framed_by writeRegions
    registers [4 => ⟨64, fr.rsp - 120⟩, 234 => ⟨64, (v234 w)⟩, 362 => ⟨64, (v362 w)⟩, 365 => ⟨64, (v365 w)⟩, 445 => ⟨64, (v445 w)⟩, 447 => ⟨64, (v447 w)⟩, 449 => ⟨64, (v449 w)⟩]
    normalize [replayAddLow, widenByte, v451, v453, v455, v457, v459, v461, v463, v465, v467, v469, v471, v474, v476, v478, v482]

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
