import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.Products

namespace K256.Proofs.Common.Point.DoubleWords.Replay

open Field AddWords Field.Multiply.SqrtSchedule Sec1.Serialize.Normalize X86Proofs

local macro "w[" i:num "]" : term =>
  `($(Lean.mkIdent (Lean.Name.mkSimple s!"w{i.getNat}"))
    $(Lean.mkIdent `p) $(Lean.mkIdent `yy) $(Lean.mkIdent `zz) $(Lean.mkIdent `sp))

private theorem doubleMask (w : Word) :
    (w + w) &&& 0x1ffffffffffffe = (w &&& 0xfffffffffffff) * 2 := by
  rw [show w + w = w <<< 1 by rw [BitVec.shiftLeft_eq_mul_twoPow]; bv_omega]
  change (w <<< 1) &&& ((0xfffffffffffff : Word) <<< 1) = _
  rw [← BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_eq_mul_twoPow]
  rfl

private theorem mask48_multiple8 (w : Word) :
    (w * 8) &&& 0xfffffffffff8 = (w * 8) &&& 0xffffffffffff := by
  have he : (w * 8) &&& 7 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change (((w * 8).toNat &&& (2^3 - 1))) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, show (8 : Word).toNat = 8 by decide +kernel]
    omega
  have hc : (w * 8) &&& ~~~(7 : Word) = w * 8 := by
    have h : (w * 8) = (((w * 8) &&& 7) ||| ((w * 8) &&& ~~~(7 : Word))) := by
      rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
    rw [he] at h
    change (w * 8) = (0#64) ||| ((w * 8) &&& ~~~(7 : Word)) at h
    rw [BitVec.zero_or] at h
    exact h.symm
  change (w * 8) &&& (~~~(7 : Word) &&& 0xffffffffffff) = _
  rw [← BitVec.and_assoc, hc]

private theorem mask48_multiple24 (w : Word) :
    (w * 24) &&& 0xfffffffffff8 = (w * 24) &&& 0xffffffffffff := by
  rw [show w * 24 = (w * 3) * 8 by rw [BitVec.mul_assoc]; rfl]
  exact mask48_multiple8 _

private theorem high_of_mulEight (w : Word) (bound : w.toNat < 2^61) :
    w >>> 45 = (w * 8) >>> 48 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul]
  change w.toNat / 2^45 = (w.toNat * 8 % 2^64) / 2^48
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem minusSource (c y n : Word) : c + y - n = y + (c - n) := by
  rw [BitVec.add_comm c y, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1500000 in
theorem doublingSources (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[326], w[339], w[349], w[363], w[368]] =
      sum yy (negate 1 (weak (scale 3 (weak (scale 21 zz))))) ∧
    #v[w[398], w[400], w[407], w[411], w[415]] = sum yy (weak (scale 21 zz)) := by
  let scaled := scale 21 zz
  have h267 : w[267] = scaled[0] := by
    simp only [w22, w28, w264, w265, w266, w267, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h283 : w[283] = scaled[1] := by
    simp only [w23, w28, w280, w281, w282, w283, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h293 : w[293] = scaled[2] := by
    simp only [w24, w28, w290, w291, w292, w293, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h301 : w[301] = scaled[3] := by
    simp only [w25, w28, w298, w299, w300, w301, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h273 : w[273] = scaled[4] := by
    simp only [w26, w28, w270, w271, w272, w273, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  let triple := weak scaled
  have h310 : w[310] = triple[0] := by
    simp only [w59, w160, w274, w275, w276, w310, h267, h273, triple, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h327 : w[327] = triple[1] := by
    simp only [w59, w160, w274, w275, w276, w285, w286, w327, h267, h273, h283, triple, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h340 : w[340] = triple[2] := by
    simp only [w59, w160, w274, w275, w276, w285, w286, w294, w295, w340, h267, h273, h283, h293, triple, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h350 : w[350] = triple[3] := by
    simp only [w59, w160, w274, w275, w276, w285, w286, w294, w295, w303, w304, w350, h267, h273, h283, h293, h301, triple, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h308 : w[308] = triple[4] := by
    simp only [w160, w257, w274, w275, w276, w285, w286, w294, w295, w303, w304, w306, w307, w308, h267, h273, h283, h293, h301, triple, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  let scaledAgain := scale 3 triple
  have h318 : w[318] = scaledAgain[0] := by
    simp only [w312, w317, w318, h310, scaledAgain, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h330 : w[330] = scaledAgain[1] := by
    simp only [w312, w329, w330, h327, scaledAgain, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h343 : w[343] = scaledAgain[2] := by
    simp only [w312, w342, w343, h340, scaledAgain, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h353 : w[353] = scaledAgain[3] := by
    simp only [w312, w352, w353, h350, scaledAgain, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h314 : w[314] = scaledAgain[4] := by
    simp only [w312, w313, w314, h308, scaledAgain, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  let nine := weak scaledAgain
  have h321 : w[321] = nine[0] := by
    simp only [w59, w160, w315, w316, w319, w321, h314, h318, nine, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h333 : w[333] = nine[1] := by
    simp only [w59, w160, w315, w316, w319, w328, w331, w333, h314, h318, h330, nine, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h346 : w[346] = nine[2] := by
    simp only [w59, w160, w315, w316, w319, w328, w331, w341, w344, w346, h314, h318, h330, h343, nine, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h360 : w[360] = nine[3] := by
    simp only [w59, w160, w315, w316, w319, w328, w331, w341, w344, w351, w354, w360, h314, h318, h330, h343, h353, nine, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h358 : w[358] = nine[4] := by
    simp only [w160, w257, w315, w316, w319, w328, w331, w341, w344, w351, w354, w356, w357, w358, h314, h318, h330, h343, h353, nine, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  let minus := sum yy (negate 1 nine)
  have h326 : w[326] = minus[0] := by
    change w[326] = yy[0] + (0x3ffffbfffff0bc - nine[0])
    simp only [w17, w322, w324, w326, h321] <;> exact minusSource _ _ _
  have h339 : w[339] = minus[1] := by
    change w[339] = yy[1] + (0x3ffffffffffffc - nine[1])
    simp only [w18, w334, w336, w337, w338, w339, h333]
    change yy[1] + (0x3ffffffffffffc : Word) - nine[1] = yy[1] + (0x3ffffffffffffc - nine[1])
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
  have h349 : w[349] = minus[2] := by
    change w[349] = yy[2] + (0x3ffffffffffffc - nine[2])
    simp only [w19, w334, w336, w337, w348, w349, h346]
    change yy[2] + (0x3ffffffffffffc : Word) - nine[2] = yy[2] + (0x3ffffffffffffc - nine[2])
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
  have h363 : w[363] = minus[3] := by
    change w[363] = yy[3] + (0x3ffffffffffffc - nine[3])
    simp only [w20, w334, w336, w337, w362, w363, h360]
    change yy[3] + (0x3ffffffffffffc : Word) - nine[3] = yy[3] + (0x3ffffffffffffc - nine[3])
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl
  have h368 : w[368] = minus[4] := by
    change w[368] = yy[4] + (0x3fffffffffffc - nine[4])
    simp only [w21, w364, w366, w368, h358] <;> exact minusSource _ _ _
  let plus := sum yy triple
  have h398 : w[398] = plus[0] := by
    simp only [w17, w398, h310, plus, sum, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h400 : w[400] = plus[1] := by
    simp only [w18, w400, h327, plus, sum, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h407 : w[407] = plus[2] := by
    simp only [w19, w407, h340, plus, sum, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h411 : w[411] = plus[3] := by
    simp only [w20, w411, h350, plus, sum, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h415 : w[415] = plus[4] := by
    simp only [w21, w415, h308, plus, sum, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  refine ⟨?_, ?_⟩
  · rw [h326, h339, h349, h363, h368]
    rfl
  · rw [h398, h400, h407, h411, h415]
    rfl

theorem xyDoubled (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[374], w[375], w[378], w[386], w[388]] =
      scale 2 (#v[w[163] &&& 0xfffffffffffff, w[202] &&& 0xfffffffffffff,
        w[240] &&& 0xfffffffffffff, w[253] &&& 0xfffffffffffff, w[260]]) := by
  rw [show w[374] = (w[163] &&& 0xfffffffffffff) * 2 from doubleMask _,
    show w[375] = (w[202] &&& 0xfffffffffffff) * 2 from doubleMask _,
    show w[378] = (w[240] &&& 0xfffffffffffff) * 2 from doubleMask _,
    show w[386] = (w[253] &&& 0xfffffffffffff) * 2 from doubleMask _,
    show w[388] = w[260] * 2 by simp only [w388]; bv_omega]
  rfl

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem correctionWords (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[639], w[640], w[643], w[644], w[637]] =
      weak (scale 24 #v[w[517], w[557], w[593], w[628], w[605]]) := by
  let raw := #v[w[517], w[557], w[593], w[628], w[605]]
  let scaled := scale 24 raw
  have h517 : w[517] = raw[0] := rfl
  have h557 : w[557] = raw[1] := rfl
  have h593 : w[593] = raw[2] := rfl
  have h628 : w[628] = raw[3] := rfl
  have h605 : w[605] = raw[4] := rfl
  have h616 : w[616] = scaled[0] := by
    simp only [w312, w613, w614, w615, w616, h517, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h621 : w[621] = scaled[1] := by
    simp only [w312, w615, w618, w619, w621, h557, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h626 : w[626] = scaled[2] := by
    simp only [w312, w615, w623, w624, w626, h593, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h632 : w[632] = scaled[3] := by
    simp only [w312, w615, w629, w630, w632, h628, scaled, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h610 : w[610] = scaled[4] := by
    simp only [w312, w608, w609, w610, h605, scaled, scale, Vector.getElem_ofFn, BitVec.shiftLeft_eq_mul_twoPow, (show BitVec.twoPow 64 3 = 8 by decide +kernel), Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h635 : w[635] = scaled[4] &&& mask48 := by
    simp only [w635, h610, w27, scaled, scale, Fin.getElem_fin, Vector.getElem_ofFn, mask48]
    exact mask48_multiple24 _
  let reduced := weak scaled
  have h639 : w[639] = reduced[0] := by
    simp only [w59, w160, w611, w612, w617, w639, h610, h616, reduced, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h640 : w[640] = reduced[1] := by
    simp only [w59, w160, w611, w612, w617, w620, w622, w640, h610, h616, h621, reduced, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h643 : w[643] = reduced[2] := by
    simp only [w59, w160, w611, w612, w617, w620, w622, w625, w627, w643, h610, h616, h621, h626, reduced, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h644 : w[644] = reduced[3] := by
    simp only [w59, w160, w611, w612, w617, w620, w622, w625, w627, w631, w633, w644, h610, h616, h621, h626, h632, reduced, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h637 : w[637] = reduced[4] := by
    simp only [w160, w611, w612, w617, w620, w622, w625, w627, w631, w633, w636, w637, h610, h616, h621, h626, h632, h635, reduced, weak, first, carry, top, mask52, mask48] <;> first | rfl | ac_rfl | bv_omega
  rw [h639, h640, h643, h644, h637]
  rfl

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem normalizedY (p : PointWords) (yy zz : Limbs) (sp : Word) :
    (output p yy zz sp).y = weak (sum
      #v[w[1411], w[1451], w[1488], w[1521], w[1500]] (scale 7 #v[w[639], w[640], w[643], w[644], w[637]])) := by
  let raw := #v[w[1411], w[1451], w[1488], w[1521], w[1500]]
  let corr := #v[w[639], w[640], w[643], w[644], w[637]]
  let sumWords := sum raw (scale 7 corr)
  have h1411 : w[1411] = raw[0] := rfl
  have h1451 : w[1451] = raw[1] := rfl
  have h1488 : w[1488] = raw[2] := rfl
  have h1521 : w[1521] = raw[3] := rfl
  have h1500 : w[1500] = raw[4] := rfl
  have h639 : w[639] = corr[0] := rfl
  have h640 : w[640] = corr[1] := rfl
  have h643 : w[643] = corr[2] := rfl
  have h644 : w[644] = corr[3] := rfl
  have h637 : w[637] = corr[4] := rfl
  have h1504 : w[1504] = sumWords[0] := by
    simp only [w615, w1502, w1503, w1504, h639, h1411, sumWords, sum, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h1507 : w[1507] = sumWords[1] := by
    simp only [w615, w1505, w1506, w1507, h640, h1451, sumWords, sum, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h1510 : w[1510] = sumWords[2] := by
    simp only [w615, w1508, w1509, w1510, h643, h1488, sumWords, sum, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h1524 : w[1524] = sumWords[3] := by
    simp only [w615, w1522, w1523, w1524, h644, h1521, sumWords, sum, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  have h1513 : w[1513] = sumWords[4] := by
    simp only [w615, w1511, w1512, w1513, h637, h1500, sumWords, sum, scale, Vector.getElem_ofFn, Fin.getElem_fin] <;> first | rfl | ac_rfl | bv_omega
  let result := weak sumWords
  have h1531 : w[1531] = result[0] := by
    simp only [w59, w160, w1514, w1515, w1516, w1531, h1504, h1513, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1532 : w[1532] = result[1] := by
    simp only [w59, w160, w1514, w1515, w1516, w1518, w1519, w1532, h1504, h1507, h1513, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1534 : w[1534] = result[2] := by
    simp only [w59, w160, w1514, w1515, w1516, w1518, w1519, w1525, w1526, w1534, h1504, h1507, h1510, h1513, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1538 : w[1538] = result[3] := by
    simp only [w59, w160, w1514, w1515, w1516, w1518, w1519, w1525, w1526, w1528, w1529, w1538, h1504, h1507, h1510, h1513, h1524, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1536 : w[1536] = result[4] := by
    simp only [w160, w257, w1514, w1515, w1516, w1518, w1519, w1525, w1526, w1528, w1529, w1533, w1535, w1536, h1504, h1507, h1510, h1513, h1524, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  change #v[w[1531], w[1532], w[1534], w[1538], w[1536]] = _
  rw [h1531, h1532, h1534, h1538, h1536]
  rfl

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem normalizedZ (p : PointWords) (yy zz : Limbs) (sp : Word)
    (bound : (w[1263]).toNat < 2^61) :
    (output p yy zz sp).z = weak (scale 8 #v[w[1167] &&& 0xfffffffffffff,
      w[1206] &&& 0xfffffffffffff, w[1244] &&& 0xfffffffffffff,
      w[1257] &&& 0xfffffffffffff, w[1263]]) := by
  let raw := #v[w[1167] &&& 0xfffffffffffff, w[1206] &&& 0xfffffffffffff,
    w[1244] &&& 0xfffffffffffff, w[1257] &&& 0xfffffffffffff, w[1263]]
  let scaled := scale 8 raw
  have shiftMask (a : Word) : (a <<< 3) &&& 0x7ffffffffffff8 = (a &&& 0xfffffffffffff) * 8 := by
    change (a <<< 3) &&& ((0xfffffffffffff : Word) <<< 3) = _
    rw [← BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_eq_mul_twoPow]
    rfl
  have h1267 : w[1267] = scaled[0] := shiftMask _
  have h1276 : w[1276] = scaled[1] := shiftMask _
  have h1281 : w[1281] = scaled[2] := shiftMask _
  have h1286 : w[1286] = scaled[3] := shiftMask _
  have h1269 : w[1269] = scaled[4] := by
    simp only [w1269, w121, w1268, w615, scaled, scale,
      Fin.getElem_fin, Vector.getElem_ofFn]
    change (0#64) + (w[1263] * 8) = w[1263] * 8
    exact BitVec.zero_add _
  have h1271 : w[1271] = scaled[4] >>> 48 := high_of_mulEight _ bound
  have h1290 : w[1290] = scaled[4] &&& mask48 := by
    simp only [w1290, h1269, w27, mask48, scaled, scale, Vector.getElem_ofFn, raw]
    exact mask48_multiple8 _
  let result := weak scaled
  have h1294 : w[1294] = result[0] := by
    simp only [w59, w160, w1272, w1273, w1294, h1267, h1271, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1295 : w[1295] = result[1] := by
    simp only [w59, w160, w1272, w1273, w1277, w1278, w1295, h1267, h1271, h1276, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1296 : w[1296] = result[2] := by
    simp only [w59, w160, w1272, w1273, w1277, w1278, w1282, w1283, w1296, h1267, h1271, h1276, h1281, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1297 : w[1297] = result[3] := by
    simp only [w59, w160, w1272, w1273, w1277, w1278, w1282, w1283, w1287, w1288, w1297, h1267, h1271, h1276, h1281, h1286, result, weak, first, carry, top, mask52] <;> first | rfl | ac_rfl | bv_omega
  have h1292 : w[1292] = result[4] := by
    simp only [w160, w1272, w1273, w1277, w1278, w1282, w1283, w1287, w1288, w1291, w1292, h1267, h1271, h1276, h1281, h1286, h1290, result, weak, first, carry, top, mask52, mask48] <;> first | rfl | ac_rfl | bv_omega
  change #v[w[1294], w[1295], w[1296], w[1297], w[1292]] = _
  rw [h1294, h1295, h1296, h1297, h1292]
  rfl

end K256.Proofs.Common.Point.DoubleWords.Replay
