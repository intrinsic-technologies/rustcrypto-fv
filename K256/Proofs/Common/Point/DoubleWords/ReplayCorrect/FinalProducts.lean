import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.Products

namespace K256.Proofs.Common.Point.DoubleWords.Replay

open Field Field.Multiply Field.Multiply.SqrtSchedule AddWords X86Proofs

local macro "w[" i:num "]" : term =>
  `($(Lean.mkIdent (Lean.Name.mkSimple s!"w{i.getNat}"))
    $(Lean.mkIdent `p) $(Lean.mkIdent `yy) $(Lean.mkIdent `zz) $(Lean.mkIdent `sp))

private theorem even_product_mask (u v : Word) :
    ((u + u) * v) &&& 0xffffffffffffe = ((u + u) * v) &&& 0xfffffffffffff := by
  rw [BitVec.add_mul]
  let t := u * v + u * v
  have even : t &&& 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change (t.toNat &&& (2^1 - 1)) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    dsimp only [t]
    rw [BitVec.toNat_add]
    omega
  have clear : t &&& ~~~(1 : Word) = t := by
    have h : t = (t &&& 1) ||| (t &&& ~~~(1 : Word)) := by
      rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
    rw [even] at h
    change t = (0#64) ||| (t &&& ~~~(1 : Word)) at h
    rw [BitVec.zero_or] at h
    exact h.symm
  change t &&& (~~~(1 : Word) &&& 0xfffffffffffff) = _
  rw [← BitVec.and_assoc, clear]

local instance : Std.Associative wideAdd := ⟨wideAdd_assoc⟩
local instance : Std.Commutative wideAdd := ⟨wideAdd_comm⟩

private theorem normalize_c8 (a : Limbs) (b : Limbs)  :
    wideMul b[4] a[4] = Product.c8 .diagonal a b := by
  simp only [Product.c8, wideMul_comm] <;> ac_rfl

private theorem normalize_d3_mask (a : Limbs) (b : Limbs) (c8 : Wide) (masked : c8.1 &&& 0xffffffffffffe = low52 c8) :
    wideAdd (wideMul (c8.1 &&& 0xffffffffffffe) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1]) (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3])))) = Product.d3 .diagonal a b c8 := by
  simp only [Product.d3, wideMul_comm, masked] <;> ac_rfl

private theorem normalize_d4_carry (a : Limbs) (b : Limbs) (c8 : Wide) (d3 : Wide) (carry : c8.2 >>> 52 = 0) :
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) ((fun w => scaleHigh w (high52 w)) c8)) (ofWord (high52 d3)) = Product.d4 .diagonal a b c8 d3 := by
  simp only [Product.d4, wideMul_comm, scaleHigh_eq carry] <;> ac_rfl

private theorem normalize_d5 (a : Limbs) (b : Limbs) (d4 : Wide)  :
    wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[2] a[3]) (wideMul b[1] a[4])) (wideMul b[3] a[2]))) (ofWord (high52 d4)) = Product.d5 .diagonal a b d4 := by
  simp only [Product.d5, wideMul_comm, wideAddRev_eq] <;> ac_rfl

private theorem normalize_r0 (a : Limbs) (b : Limbs) (d4 : Wide) (d5 : Wide)  :
    wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul b[0] a[0]) = Product.r0 .diagonal a b d4 d5 := by
  simp only [Product.r0, wideMul_comm] <;> ac_rfl

private theorem normalize_d6 (a : Limbs) (b : Limbs) (d5 : Wide)  :
    wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul b[2] a[4]))) (ofWord (high52 d5)) = Product.d6 .diagonal a b d5 := by
  simp only [Product.d6, wideMul_comm, wideAddRev_eq] <;> ac_rfl

private theorem normalize_r1 (a : Limbs) (b : Limbs) (r0 : Wide) (d6 : Wide)  :
    wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul b[0] a[1])) (wideMul (low52 d6) 0x1000003d10)) (ofWord (high52 r0)) = Product.r1 .diagonal a b r0 d6 := by
  simp only [Product.r1, wideMul_comm] <;> ac_rfl

private theorem normalize_d7_reversed (a : Limbs) (b : Limbs) (d6 : Wide)  :
    wideAdd (wideAddRev (wideMul b[4] a[3]) (wideMul b[3] a[4])) (ofWord (high52 d6)) = Product.d7 .diagonal a b d6 := by
  simp only [Product.d7, wideMul_comm, wideAddRev_eq] <;> ac_rfl

private theorem normalize_r2 (a : Limbs) (b : Limbs) (r1 : Wide) (d7 : Wide)  :
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul b[0] a[2])) (wideMul b[2] a[0])) (wideMul (low52 d7) 0x1000003d10)) (ofWord (high52 r1)) = Product.r2 .diagonal a b r1 d7 := by
  simp only [Product.r2, wideMul_comm] <;> ac_rfl

private theorem normalize_r3 (d3 : Wide) (d7 : Wide) (r2 : Wide)  :
    wideAdd (wideAddRev (ofWord (low52 d3)) (wideMul (high52 d7) 0x1000003d10)) (ofWord (high52 r2)) = Product.r3 .diagonal d3 d7 r2 := by
  simp only [Product.r3, wideMul_comm, wideAddRev_eq] <;> ac_rfl

private theorem normalize_d3 (a : Limbs) (b : Limbs) (c8 : Wide)  :
    wideAdd (wideMul (low52 c8) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1]) (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3])))) = Product.d3 .diagonal a b c8 := by
  simp only [Product.d3, wideMul_comm] <;> ac_rfl

private theorem normalize_d4 (a : Limbs) (b : Limbs) (c8 : Wide) (d3 : Wide)  :
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) (wideMul (high52 c8) 0x1000003d10)) (ofWord (high52 d3)) = Product.d4 .diagonal a b c8 d3 := by
  simp only [Product.d4, wideMul_comm] <;> ac_rfl

set_option maxHeartbeats 600000 in
theorem outX_words (p : PointWords) (yy zz : Limbs) (sp : Word)
    (top : (w[388]).toNat * (w[368]).toNat < 2^116)
    : #v[w[750] &&& 0xfffffffffffff, w[790] &&& 0xfffffffffffff, w[829] &&& 0xfffffffffffff, w[843] &&& 0xfffffffffffff, w[859]] = Product.words .diagonal (#v[w[326], w[339], w[349], w[363], w[368]]) (#v[w[374], w[375], w[378], w[386], w[388]]) := by
  let a := #v[w[326], w[339], w[349], w[363], w[368]]
  let b := #v[w[374], w[375], w[378], w[386], w[388]]
  have h326 : w[326] = a[0] := rfl
  have h339 : w[339] = a[1] := rfl
  have h349 : w[349] = a[2] := rfl
  have h363 : w[363] = a[3] := rfl
  have h368 : w[368] = a[4] := rfl
  have h374 : w[374] = b[0] := rfl
  have h375 : w[375] = b[1] := rfl
  have h378 : w[378] = b[2] := rfl
  have h386 : w[386] = b[3] := rfl
  have h388 : w[388] = b[4] := rfl
  let c8 := Product.c8 .diagonal a b
  let c8Graph := wideMul b[4] a[4]
  have c8Eq : c8Graph = c8 := normalize_c8 a b
  have h664 : w[664] = c8.1 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  have h663 : w[663] = c8.2 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  let d3 := Product.d3 .diagonal a b c8
  have hm : c8.1 &&& 0xffffffffffffe = low52 c8 := by
    change (wideMul a[4] b[4]).1 &&& 0xffffffffffffe = low52 (wideMul a[4] b[4])
    rw [wideMul_comm a[4] b[4]]
    exact even_product_mask (w[260]) (w[368])
  let d3Graph := wideAdd (wideMul (c8.1 &&& 0xffffffffffffe) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1]) (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3]))))
  have d3Eq : d3Graph = d3 := normalize_d3_mask a b c8 hm
  have h670 : w[670] = d3.1 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  have h673 : w[673] = d3.2 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  let d4 := Product.d4 .diagonal a b c8 d3
  have hc : c8.2 >>> 52 = 0 := by
    rw [show c8 = wideMul b[4] a[4] from wideMul_comm _ _]
    exact top_product_shift_zero top
  let d4Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) ((fun w => scaleHigh w (high52 w)) c8)) (ofWord (high52 d3))
  have d4Eq : d4Graph = d4 := normalize_d4_carry a b c8 d3 hc
  have h711 : w[711] = d4.1 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  have h714 : w[714] = d4.2 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  let d5 := Product.d5 .diagonal a b d4
  let d5Graph := wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[2] a[3]) (wideMul b[1] a[4])) (wideMul b[3] a[2]))) (ofWord (high52 d4))
  have d5Eq : d5Graph = d5 := normalize_d5 a b d4
  have h740 : w[740] = d5.1 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  have h743 : w[743] = d5.2 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  let r0 := Product.r0 .diagonal a b d4 d5
  let r0Graph := wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul b[0] a[0])
  have r0Eq : r0Graph = r0 := normalize_r0 a b d4 d5
  have h750 : w[750] = r0.1 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  have h753 : w[753] = r0.2 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  let d6 := Product.d6 .diagonal a b d5
  let d6Graph := wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul b[2] a[4]))) (ofWord (high52 d5))
  have d6Eq : d6Graph = d6 := normalize_d6 a b d5
  have h774 : w[774] = d6.1 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  have h777 : w[777] = d6.2 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  let r1 := Product.r1 .diagonal a b r0 d6
  let r1Graph := wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul b[0] a[1])) (wideMul (low52 d6) 0x1000003d10)) (ofWord (high52 r0))
  have r1Eq : r1Graph = r1 := normalize_r1 a b r0 d6
  have h790 : w[790] = r1.1 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  have h793 : w[793] = r1.2 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  let d7 := Product.d7 .diagonal a b d6
  let d7Graph := wideAdd (wideAddRev (wideMul b[4] a[3]) (wideMul b[3] a[4])) (ofWord (high52 d6))
  have d7Eq : d7Graph = d7 := normalize_d7_reversed a b d6
  have h810 : w[810] = d7.1 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  have h813 : w[813] = d7.2 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  let r2 := Product.r2 .diagonal a b r1 d7
  let r2Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul b[0] a[2])) (wideMul b[2] a[0])) (wideMul (low52 d7) 0x1000003d10)) (ofWord (high52 r1))
  have r2Eq : r2Graph = r2 := normalize_r2 a b r1 d7
  have h829 : w[829] = r2.1 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  have h832 : w[832] = r2.2 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  let r3 := Product.r3 .diagonal d3 d7 r2
  let r3Graph := wideAdd (wideAddRev (ofWord (low52 d3)) (wideMul (high52 d7) 0x1000003d10)) (ofWord (high52 r2))
  have r3Eq : r3Graph = r3 := normalize_r3 d3 d7 r2
  have h843 : w[843] = r3.1 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have h846 : w[846] = r3.2 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have limb0 : w[750] &&& 0xfffffffffffff = low52 r0 := by double_product_word []
  have limb1 : w[790] &&& 0xfffffffffffff = low52 r1 := by double_product_word []
  have limb2 : w[829] &&& 0xfffffffffffff = low52 r2 := by double_product_word []
  have limb3 : w[843] &&& 0xfffffffffffff = low52 r3 := by double_product_word []
  have limb4 : w[859] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

set_option maxHeartbeats 600000 in
theorem outZ_words (p : PointWords) (yy zz : Limbs) (sp : Word)
    (top : (w[1050]).toNat * (w[16]).toNat < 2^116)
    : #v[w[1167] &&& 0xfffffffffffff, w[1206] &&& 0xfffffffffffff, w[1244] &&& 0xfffffffffffff, w[1257] &&& 0xfffffffffffff, w[1263]] = Product.words .diagonal (#v[w[12], w[13], w[14], w[15], w[16]]) (#v[w[1052], w[1053], w[1054], w[1055], w[1050]]) := by
  let a := #v[w[12], w[13], w[14], w[15], w[16]]
  let b := #v[w[1052], w[1053], w[1054], w[1055], w[1050]]
  have h12 : w[12] = a[0] := rfl
  have h13 : w[13] = a[1] := rfl
  have h14 : w[14] = a[2] := rfl
  have h15 : w[15] = a[3] := rfl
  have h16 : w[16] = a[4] := rfl
  have h1052 : w[1052] = b[0] := rfl
  have h1053 : w[1053] = b[1] := rfl
  have h1054 : w[1054] = b[2] := rfl
  have h1055 : w[1055] = b[3] := rfl
  have h1050 : w[1050] = b[4] := rfl
  let c8 := Product.c8 .diagonal a b
  let c8Graph := wideMul b[4] a[4]
  have c8Eq : c8Graph = c8 := normalize_c8 a b
  have h1082 : w[1082] = c8.1 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  have h1081 : w[1081] = c8.2 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  let d3 := Product.d3 .diagonal a b c8
  let d3Graph := wideAdd (wideMul (low52 c8) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1]) (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3]))))
  have d3Eq : d3Graph = d3 := normalize_d3 a b c8
  have h1087 : w[1087] = d3.1 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  have h1090 : w[1090] = d3.2 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  let d4 := Product.d4 .diagonal a b c8 d3
  have hc : c8.2 >>> 52 = 0 := by
    rw [show c8 = wideMul b[4] a[4] from wideMul_comm _ _]
    exact top_product_shift_zero top
  let d4Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) ((fun w => scaleHigh w (high52 w)) c8)) (ofWord (high52 d3))
  have d4Eq : d4Graph = d4 := normalize_d4_carry a b c8 d3 hc
  have h1128 : w[1128] = d4.1 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  have h1131 : w[1131] = d4.2 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  let d5 := Product.d5 .diagonal a b d4
  let d5Graph := wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[2] a[3]) (wideMul b[1] a[4])) (wideMul b[3] a[2]))) (ofWord (high52 d4))
  have d5Eq : d5Graph = d5 := normalize_d5 a b d4
  have h1157 : w[1157] = d5.1 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  have h1160 : w[1160] = d5.2 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  let r0 := Product.r0 .diagonal a b d4 d5
  let r0Graph := wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul b[0] a[0])
  have r0Eq : r0Graph = r0 := normalize_r0 a b d4 d5
  have h1167 : w[1167] = r0.1 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  have h1170 : w[1170] = r0.2 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  let d6 := Product.d6 .diagonal a b d5
  let d6Graph := wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul b[2] a[4]))) (ofWord (high52 d5))
  have d6Eq : d6Graph = d6 := normalize_d6 a b d5
  have h1190 : w[1190] = d6.1 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  have h1193 : w[1193] = d6.2 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  let r1 := Product.r1 .diagonal a b r0 d6
  let r1Graph := wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul b[0] a[1])) (wideMul (low52 d6) 0x1000003d10)) (ofWord (high52 r0))
  have r1Eq : r1Graph = r1 := normalize_r1 a b r0 d6
  have h1206 : w[1206] = r1.1 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  have h1209 : w[1209] = r1.2 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  let d7 := Product.d7 .diagonal a b d6
  let d7Graph := wideAdd (wideAddRev (wideMul b[4] a[3]) (wideMul b[3] a[4])) (ofWord (high52 d6))
  have d7Eq : d7Graph = d7 := normalize_d7_reversed a b d6
  have h1225 : w[1225] = d7.1 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  have h1228 : w[1228] = d7.2 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  let r2 := Product.r2 .diagonal a b r1 d7
  let r2Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul b[0] a[2])) (wideMul b[2] a[0])) (wideMul (low52 d7) 0x1000003d10)) (ofWord (high52 r1))
  have r2Eq : r2Graph = r2 := normalize_r2 a b r1 d7
  have h1244 : w[1244] = r2.1 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  have h1247 : w[1247] = r2.2 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  let r3 := Product.r3 .diagonal d3 d7 r2
  let r3Graph := wideAdd (wideAddRev (ofWord (low52 d3)) (wideMul (high52 d7) 0x1000003d10)) (ofWord (high52 r2))
  have r3Eq : r3Graph = r3 := normalize_r3 d3 d7 r2
  have h1257 : w[1257] = r3.1 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have h1260 : w[1260] = r3.2 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have limb0 : w[1167] &&& 0xfffffffffffff = low52 r0 := by double_product_word []
  have limb1 : w[1206] &&& 0xfffffffffffff = low52 r1 := by double_product_word []
  have limb2 : w[1244] &&& 0xfffffffffffff = low52 r2 := by double_product_word []
  have limb3 : w[1257] &&& 0xfffffffffffff = low52 r3 := by double_product_word []
  have limb4 : w[1263] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

set_option maxHeartbeats 600000 in
theorem outY_words (p : PointWords) (yy zz : Limbs) (sp : Word)
    : #v[w[1400] &&& 0xfffffffffffff, w[1440] &&& 0xfffffffffffff, w[1480] &&& 0xfffffffffffff, w[1494] &&& 0xfffffffffffff, w[1500]] = Product.words .diagonal (#v[w[398], w[400], w[407], w[411], w[415]]) (#v[w[326], w[339], w[349], w[363], w[368]]) := by
  let a := #v[w[398], w[400], w[407], w[411], w[415]]
  let b := #v[w[326], w[339], w[349], w[363], w[368]]
  have h398 : w[398] = a[0] := rfl
  have h400 : w[400] = a[1] := rfl
  have h407 : w[407] = a[2] := rfl
  have h411 : w[411] = a[3] := rfl
  have h415 : w[415] = a[4] := rfl
  have h326 : w[326] = b[0] := rfl
  have h339 : w[339] = b[1] := rfl
  have h349 : w[349] = b[2] := rfl
  have h363 : w[363] = b[3] := rfl
  have h368 : w[368] = b[4] := rfl
  let c8 := Product.c8 .diagonal a b
  let c8Graph := wideMul b[4] a[4]
  have c8Eq : c8Graph = c8 := normalize_c8 a b
  have h1319 : w[1319] = c8.1 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  have h1318 : w[1318] = c8.2 := by
    rw [← c8Eq]
    double_product_word [c8Graph]
  let d3 := Product.d3 .diagonal a b c8
  let d3Graph := wideAdd (wideMul (low52 c8) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1]) (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3]))))
  have d3Eq : d3Graph = d3 := normalize_d3 a b c8
  have h1324 : w[1324] = d3.1 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  have h1327 : w[1327] = d3.2 := by
    rw [← d3Eq]
    double_product_word [d3Graph]
  let d4 := Product.d4 .diagonal a b c8 d3
  let d4Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) (wideMul (high52 c8) 0x1000003d10)) (ofWord (high52 d3))
  have d4Eq : d4Graph = d4 := normalize_d4 a b c8 d3
  have h1361 : w[1361] = d4.1 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  have h1364 : w[1364] = d4.2 := by
    rw [← d4Eq]
    double_product_word [d4Graph]
  let d5 := Product.d5 .diagonal a b d4
  let d5Graph := wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[2] a[3]) (wideMul b[1] a[4])) (wideMul b[3] a[2]))) (ofWord (high52 d4))
  have d5Eq : d5Graph = d5 := normalize_d5 a b d4
  have h1390 : w[1390] = d5.1 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  have h1393 : w[1393] = d5.2 := by
    rw [← d5Eq]
    double_product_word [d5Graph]
  let r0 := Product.r0 .diagonal a b d4 d5
  let r0Graph := wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul b[0] a[0])
  have r0Eq : r0Graph = r0 := normalize_r0 a b d4 d5
  have h1400 : w[1400] = r0.1 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  have h1403 : w[1403] = r0.2 := by
    rw [← r0Eq]
    double_product_word [r0Graph]
  let d6 := Product.d6 .diagonal a b d5
  let d6Graph := wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul b[2] a[4]))) (ofWord (high52 d5))
  have d6Eq : d6Graph = d6 := normalize_d6 a b d5
  have h1424 : w[1424] = d6.1 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  have h1427 : w[1427] = d6.2 := by
    rw [← d6Eq]
    double_product_word [d6Graph]
  let r1 := Product.r1 .diagonal a b r0 d6
  let r1Graph := wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul b[0] a[1])) (wideMul (low52 d6) 0x1000003d10)) (ofWord (high52 r0))
  have r1Eq : r1Graph = r1 := normalize_r1 a b r0 d6
  have h1440 : w[1440] = r1.1 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  have h1443 : w[1443] = r1.2 := by
    rw [← r1Eq]
    double_product_word [r1Graph]
  let d7 := Product.d7 .diagonal a b d6
  let d7Graph := wideAdd (wideAddRev (wideMul b[4] a[3]) (wideMul b[3] a[4])) (ofWord (high52 d6))
  have d7Eq : d7Graph = d7 := normalize_d7_reversed a b d6
  have h1460 : w[1460] = d7.1 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  have h1463 : w[1463] = d7.2 := by
    rw [← d7Eq]
    double_product_word [d7Graph]
  let r2 := Product.r2 .diagonal a b r1 d7
  let r2Graph := wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul b[0] a[2])) (wideMul b[2] a[0])) (wideMul (low52 d7) 0x1000003d10)) (ofWord (high52 r1))
  have r2Eq : r2Graph = r2 := normalize_r2 a b r1 d7
  have h1480 : w[1480] = r2.1 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  have h1483 : w[1483] = r2.2 := by
    rw [← r2Eq]
    double_product_word [r2Graph]
  let r3 := Product.r3 .diagonal d3 d7 r2
  let r3Graph := wideAdd (wideAddRev (ofWord (low52 d3)) (wideMul (high52 d7) 0x1000003d10)) (ofWord (high52 r2))
  have r3Eq : r3Graph = r3 := normalize_r3 d3 d7 r2
  have h1494 : w[1494] = r3.1 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have h1497 : w[1497] = r3.2 := by
    rw [← r3Eq]
    double_product_word [r3Graph]
  have limb0 : w[1400] &&& 0xfffffffffffff = low52 r0 := by double_product_word []
  have limb1 : w[1440] &&& 0xfffffffffffff = low52 r1 := by double_product_word []
  have limb2 : w[1480] &&& 0xfffffffffffff = low52 r2 := by double_product_word []
  have limb3 : w[1494] &&& 0xfffffffffffff = low52 r3 := by double_product_word []
  have limb4 : w[1500] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

end K256.Proofs.Common.Point.DoubleWords.Replay
