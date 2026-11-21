import K256.Proofs.Sec1.Affine.Uncompressed.SquareWords
import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Wide

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field K256.Proofs.Common.Field.Multiply
  K256.Proofs.Common.Field.Multiply.SqrtSchedule X86Proofs

private abbrev wideDouble (w : Wide) : Wide := (w.1 + w.1, shldResult 1 w.2 w.1)

private theorem wideValue_injective {a b : Wide} (h : wideValue a = wideValue b) : a = b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · exact (SquareValue.lo_toNat a.1 a.2).trans
      ((congrArg (· % 2^64) h).trans (SquareValue.lo_toNat b.1 b.2).symm)
  · have ha := a.1.isLt
    have hb := b.1.isLt
    simp only [wideValue, pairNat] at h
    omega

private theorem mulDouble (a b : Word) (ha : a.toNat < 2^63)
    (hab : 2 * (a.toNat * b.toNat) < 2^128) :
    wideMul (a + a) b = wideDouble (wideMul b a) := by
  apply wideValue_injective
  change pairNat ((a+a)*b) (mulResult (a+a) b).2 =
    pairNat (b*a+b*a) (shldResult 1 (mulResult b a).2 (b*a))
  rw [SquareValue.pair_mul, SquareValue.pair_dbl]
  · rw [SquareValue.pair_mul, Nat.mul_comm b.toNat]
    have h : (a + a).toNat = 2 * a.toNat := by rw [BitVec.toNat_add_of_lt (by omega)]; omega
    rw [h, Nat.mul_assoc]
  · rwa [SquareValue.pair_mul, Nat.mul_comm b.toNat]

private theorem bounded (w : Word) : BoundedValue w.toNat w.toNat (2^64-1) :=
  ⟨rfl, Nat.le_sub_one_of_lt w.isLt⟩

private theorem limbBound {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) (i : Fin 5) :
    BoundedValue a[i].toNat a[i].toNat (2^56 - 1) := by
  refine ⟨rfl, ?_⟩
  have hi := h.1 i
  by_cases hi4 : i.val < 4
  · have hb : a[i].toNat ≤ 2 * 8 * (2^52 - 1) := by
      simpa only [hi4, ite_true, getElem!_pos, i.isLt] using hi
    omega
  · have hb : a[i].toNat ≤ 2 * 8 * (2^48 - 1) := by
      simpa only [hi4, ite_false, getElem!_pos, i.isLt] using hi
    omega

private theorem double_limb_bound {w : Word} {n : Nat}
    (h : BoundedValue w.toNat n (2^56 - 1)) :
    BoundedValue (w+w).toNat (n+n) (2 * (2^56 - 1)) :=
  h.wordAdd h

private theorem boundDouble {w : Wide} {n m : Nat} (h : BoundedValue (wideValue w) n m)
    (hm : 2*m < 2^128 := by decide) :
    BoundedValue (wideValue (wideDouble w)) (2*n) (2*m) := by
  refine ⟨?_, Nat.mul_le_mul_left 2 h.le⟩
  have hb : 2 * pairNat w.1 w.2 < 2^128 := by
    change 2 * wideValue w < _
    rw [h.eq]
    have hn := h.le
    omega
  exact (SquareValue.pair_dbl w.1 w.2 hb).trans (congrArg (2 * ·) h.eq)

private theorem carryHighZero (w : Wide) {n m : Nat} (hw : BoundedValue (wideValue w) n m)
    (hm : m < 2^116 := by decide) : w.2 >>> 52 = 0 := by
  have ht : wideValue w < 2^116 := hw.eq ▸ Nat.lt_of_le_of_lt hw.le hm
  simp only [wideValue, pairNat] at ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w.2.toNat / 2^52 = 0
  omega

private theorem limbShiftZero (w : Word) {n : Nat} (h : BoundedValue w.toNat n (2^56 - 1)) :
    w >>> 63 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w.toNat / 2^63 = 0
  have hw := h.eq ▸ h.le
  omega

private theorem combine56_eq (a b : Wide) :
    a.1 <<< 4 &&& (72057594037927920 : Word) |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (b.1 >>> 48)) &&& 15) = combine56 a b := by
  unfold combine56
  rw [BitVec.setWidth_and]
  rfl

private def squareAcc3 (a : Limbs) : Wide :=
  wideAdd (wideMul (4503599627370493 &&& (wideMul a[4] a[4]).1) 68719492368)
    (wideDouble (wideAdd (wideMul a[2] a[1]) (wideMul a[3] a[0])))

private def squareAcc4 (a : Limbs) (d3 : Wide) : Wide :=
  wideAdd (wideAdd (wideAdd (wideMul (high52 (wideMul a[4] a[4])) 68719492368) (wideMul a[2] a[2]))
    (wideDouble (wideAdd (wideMul a[3] a[1]) (wideMul a[4] a[0])))) (ofWord (high52 d3))

private def squareAcc5 (a : Limbs) (d4 : Wide) : Wide :=
  wideAdd (wideDouble (wideAdd (wideMul a[4] a[1]) (wideMul a[3] a[2]))) (ofWord (high52 d4))

private def squareAcc6 (a : Limbs) (d5 : Wide) : Wide :=
  wideAdd (wideAdd (wideMul (a[4]+a[4]) a[2]) (wideMul a[3] a[3])) (ofWord (high52 d5))

private def squareAcc7 (a : Limbs) (d6 : Wide) : Wide :=
  wideAdd (wideMul (a[4]+a[4]) a[3]) (ofWord (high52 d6))

private def squareOut0 (a : Limbs) (d4 d5 : Wide) : Wide :=
  wideAdd (wideMul (combine56 d5 d4) 4294968273) (wideMul a[0] a[0])

private def squareOut1 (a : Limbs) (d6 r0 : Wide) : Wide :=
  wideAdd (wideAdd (wideMul (low52 d6) 68719492368) (wideMul (a[0]+a[0]) a[1])) (ofWord (high52 r0))

private def squareOut2Partial (a : Limbs) (d7 : Wide) : Wide :=
  wideAdd (wideAdd (wideMul (a[0]+a[0]) a[2]) (wideMul a[1] a[1]))
    (wideMul (low52 d7) 68719492368)

private def squareOut2 (a : Limbs) (d7 r1 : Wide) : Wide :=
  wideAdd (squareOut2Partial a d7) (ofWord (high52 r1))

private def squareOut3 (d3 d7 r2 : Wide) : Wide :=
  wideAdd (wideAdd (ofWord (4503599627370494 &&& d3.1)) (wideMul (high52 d7) 68719492368))
    (ofWord (high52 r2))

private def squaredLimbs (a : Limbs) : Limbs :=
  let d3 := squareAcc3 a
  let d4 := squareAcc4 a d3
  let d5 := squareAcc5 a d4
  let d6 := squareAcc6 a d5
  let d7 := squareAcc7 a d6
  let r0 := squareOut0 a d4 d5
  let r1 := squareOut1 a d6 r0
  let r2 := squareOut2 a d7 r1
  let r3 := squareOut3 d3 d7 r2
  #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]

private theorem shiftBounds {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) :
    let d3 := squareAcc3 a
    let d4 := squareAcc4 a d3
    let d5 := squareAcc5 a d4
    let d6 := squareAcc6 a d5
    let d7 := squareAcc7 a d6
    let r0 := squareOut0 a d4 d5
    let r1 := squareOut1 a d6 r0
    let r2 := squareOut2 a d7 r1
    d3.2 >>> 52 = 0 ∧ d4.2 >>> 52 = 0 ∧ d5.2 >>> 52 = 0 ∧ d6.2 >>> 52 = 0 ∧
      r1.2 >>> 52 = 0 ∧ r2.2 >>> 52 = 0 := by
  dsimp only
  let h0 := limbBound h 0
  let h1 := limbBound h 1
  let h2 := limbBound h 2
  let h3 := limbBound h 3
  let h4 := limbBound h 4
  have hR : BoundedValue (68719492368 : Word).toNat 68719492368 68719492368 :=
    ⟨rfl, Nat.le_refl _⟩
  let d3 := squareAcc3 a
  let d4 := squareAcc4 a d3
  let d5 := squareAcc5 a d4
  let d6 := squareAcc6 a d5
  let d7 := squareAcc7 a d6
  let r0 := squareOut0 a d4 d5
  let r1 := squareOut1 a d6 r0
  have hd3 := ((bounded (4503599627370493 &&& (wideMul a[4] a[4]).1)).wideMul hR).wideAdd
    (boundDouble ((h2.wideMul h1).wideAdd (h3.wideMul h0)))
  have hd4 := (((bounded (high52 (wideMul a[4] a[4]))).wideMul hR).wideAdd (h2.wideMul h2)).wideAdd
    (boundDouble ((h3.wideMul h1).wideAdd (h4.wideMul h0)))
  have hd4' := hd4.wideAdd (bounded (high52 d3)).ofWord
  have hd5 := (boundDouble ((h4.wideMul h1).wideAdd (h3.wideMul h2))).wideAdd (bounded (high52 d4)).ofWord
  have hd6 := (((double_limb_bound h4).wideMul h2).wideAdd (h3.wideMul h3)).wideAdd
    (bounded (high52 d5)).ofWord
  have hr1 := (((bounded (low52 d6)).wideMul hR).wideAdd ((double_limb_bound h0).wideMul h1)).wideAdd
    (bounded (high52 r0)).ofWord
  have hr2 := ((((double_limb_bound h0).wideMul h2).wideAdd (h1.wideMul h1)).wideAdd
    ((bounded (low52 d7)).wideMul hR)).wideAdd (bounded (high52 r1)).ofWord
  exact ⟨carryHighZero _ hd3, carryHighZero _ hd4', carryHighZero _ hd5, carryHighZero _ hd6,
    carryHighZero _ hr1, carryHighZero _ hr2⟩

private abbrev carryPair (p : Wide) : Wide := (high52 p, p.2 >>> 52)

private theorem carryPair_eq (p : Wide) (h : p.2 >>> 52 = 0) :
    carryPair p = ofWord (high52 p) := congrArg (fun hi => (high52 p, hi)) h

private abbrev wideAddWordMachine (p : Wide) (w : Word) : Wide :=
  (p.1 + w, p.2 + 0 + SquareValue.cf p.1 w)

private theorem d3MaskSwap (a : Word) :
    a &&& 4503599627370493 = 4503599627370493 &&& a := BitVec.and_comm _ _

private theorem d3EvenMaskSwap (a : Word) :
    a &&& 4503599627370494 = 4503599627370494 &&& a := BitVec.and_comm _ _

private theorem low52_swap (p : Wide) :
    (4503599627370495 : Word) &&& p.1 = low52 p := BitVec.and_comm _ _

private theorem low48_swap (p : Wide) :
    (281474976710655 : Word) &&& p.1 = low48 p := BitVec.and_comm _ _

private theorem congrWide {α : Type} (f : Wide → Wide → α) {a b c d : Wide}
    (h₀ : a = b) (h₁ : c = d) : f a c = f b d := by
  cases h₀
  cases h₁
  rfl

private theorem squareXCut1 (a : Limbs) :
    let d3 := squareAcc3 a
    squareX11FBD1H a =
      #v[d3.1, d3.2, high52 d3, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
          (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
          (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] := by
  intro d3
  let d := wideAddRev (wideMul (4503599627370493 &&& (wideMul a[4] a[4]).1) 68719492368) (wideDouble (wideAddRev (wideMul a[2] a[1]) (wideMul a[3] a[0])))
  change #v[d.1, d.2, high52 d, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] = _
  have hd : d = d3 := by simp only [d, d3, squareAcc3, wideAddRev_eq] <;> rfl
  exact congrArg (fun d : Wide => #v[d.1, d.2, high52 d, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2]) hd

private theorem squareXCut2 (a : Limbs) (d3 : Wide) (h3 : d3.2 >>> 52 = 0) :
    let d4 := squareAcc4 a d3
    squareX11FC4F a #v[d3.1, d3.2, high52 d3, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
        (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
        (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] =
      #v[d3.1, d4.1, high52 d4, d4.2 >>> 52, d4.1 >>> 48, (wideMul a[0] a[0]).2, (wideMul a[0] a[0]).1,
          (wideMul a[3] a[2]).2] := by
  intro d4
  let cross := wideDouble (wideAddRev (wideMul a[3] a[1]) (wideMul a[4] a[0]))
  let sq := wideAdd (wideMul (high52 (wideMul a[4] a[4])) 68719492368) (wideMul a[2] a[2])
  let d := wideAdd (wideAddRev cross sq) (carryPair d3)
  change #v[d3.1, d.1, high52 d, d.2 >>> 52, d.1 >>> 48, (wideMul a[0] a[0]).2, (wideMul a[0] a[0]).1,
      (wideMul a[3] a[2]).2] = _
  have e : wideAddRev cross sq = wideAdd sq cross :=
    (wideAddRev_eq _ _).trans (wideAdd_comm _ _)
  have hd : d = d4 := by
    simp only [d, e, carryPair_eq d3 h3]
    simp only [cross, sq, d4, squareAcc4, wideAddRev_eq]
  exact congrArg (fun d : Wide => #v[d3.1, d.1, high52 d, d.2 >>> 52, d.1 >>> 48, (wideMul a[0] a[0]).2,
      (wideMul a[0] a[0]).1, (wideMul a[3] a[2]).2]) hd

private theorem squareXCut3 (a : Limbs) (d3 d4 : Wide) (h4 : d4.2 >>> 52 = 0) :
    let d5 := squareAcc5 a d4
    let r0 := squareOut0 a d4 d5
    squareX11FCAB a #v[d3.1, d4.1, high52 d4, d4.2 >>> 52, d4.1 >>> 48, (wideMul a[0] a[0]).2,
        (wideMul a[0] a[0]).1, (wideMul a[3] a[2]).2] =
      #v[d3.1, d4.1, high52 d5, d5.2 >>> 52, r0.1, high52 r0, a[0] + a[0]] := by
  intro d5 r0
  let d := wideAdd (wideDouble (wideAddRev (wideMul a[4] a[1]) (wideMul a[3] a[2]))) (carryPair d4)
  let r := wideAddRev (wideMul ((d.1 <<< 4 &&& (72057594037927920 : Word) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (d4.1 >>> 48)) &&& 15))) 4294968273) (wideMul a[0] a[0])
  change #v[d3.1, d4.1, high52 d, d.2 >>> 52, r.1, high52 r, a[0] + a[0]] = _
  have hd : d = d5 := by
    simp only [d, d5, squareAcc5, wideAddRev_eq, carryPair_eq d4 h4]
  have hr : r = r0 := by
    simp only [r, r0, squareOut0, hd, wideAddRev_eq, combine56_eq] <;> rfl
  exact congrWide (fun d r => #v[d3.1, d4.1, high52 d, d.2 >>> 52, r.1, high52 r, a[0] + a[0]]) hd hr

private theorem squareXCut4 (a : Limbs) (d3 d4 d5 r0 : Wide) (h5 : d5.2 >>> 52 = 0) :
    let d6 := squareAcc6 a d5
    let r1 := squareOut1 a d6 r0
    squareX11FD1DH a #v[d3.1, d4.1, high52 d5, d5.2 >>> 52, r0.1, high52 r0, a[0] + a[0]] =
      #v[d3.1, d4.1, r0.1, a[0] + a[0], a[4] + a[4], r1.1, r1.2, high52 d6, d6.2 >>> 52] := by
  intro d6 r1
  let d := wideAdd (wideAddRev (wideMul (a[4] + a[4]) a[2]) (wideMul a[3] a[3])) (carryPair d5)
  let r := wideAddWordMachine (wideAddRev (wideMul (low52 d) 68719492368) (wideMul (a[0] + a[0]) a[1])) (high52 r0)
  change #v[d3.1, d4.1, r0.1, a[0] + a[0], a[4] + a[4], r.1, r.2, high52 d, d.2 >>> 52] = _
  have hd : d = d6 := by
    simp only [d, d6, squareAcc6, wideAddRev_eq, carryPair_eq d5 h5]
  have hr : r = r1 := by
    simp only [r, r1, squareOut1, hd, wideAddRev_eq] <;> rfl
  exact congrWide (fun d r => #v[d3.1, d4.1, r0.1, a[0] + a[0], a[4] + a[4], r.1, r.2, high52 d, d.2 >>> 52]) hd hr

private theorem squareXCut5 (a : Limbs) (d3 d4 d6 r0 r1 : Wide) (h6 : d6.2 >>> 52 = 0) (h1 : r1.2 >>> 52 = 0) :
    let d7 := squareAcc7 a d6
    let r2 := squareOut2 a d7 r1
    squareX11FD89 a #v[d3.1, d4.1, r0.1, a[0] + a[0], a[4] + a[4], r1.1, r1.2, high52 d6, d6.2 >>> 52] =
      #v[d3.1, d4.1, r0.1, r1.1, r2.1, r2.2, high52 d7] := by
  intro d7 r2
  let d := wideAddRev (wideMul (a[4] + a[4]) a[3]) (carryPair d6)
  let q := wideAdd (wideAddRev (wideMul (a[0] + a[0]) a[2]) (wideMul a[1] a[1])) (wideMul (low52 d) 68719492368)
  let r := wideAdd q (carryPair r1)
  change #v[d3.1, d4.1, r0.1, r1.1, r.1, r.2, high52 d] = _
  have hd : d = d7 := by
    simp only [d, d7, squareAcc7, wideAddRev_eq, carryPair_eq d6 h6]
  have hr : r = r2 := by
    simp only [q, r, r2, squareOut2, squareOut2Partial, hd, wideAddRev_eq, carryPair_eq r1 h1]
  exact congrWide (fun d r => #v[d3.1, d4.1, r0.1, r1.1, r.1, r.2, high52 d]) hd hr

private theorem squareXCut6 (d3 d4 d7 r0 r1 r2 : Wide) (h2 : r2.2 >>> 52 = 0) :
    let r3 := squareOut3 d3 d7 r2
    squareX11FDF2 #v[d3.1, d4.1, r0.1, r1.1, r2.1, r2.2, high52 d7] =
      #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3] := by
  intro r3
  let r := wideAddRev (wideAdd (wideMul (high52 d7) 68719492368) (ofWord (d3.1 &&& 4503599627370494))) (carryPair r2)
  change #v[low52 r0, low52 r1, low52 r2, low52 r,
      low48 d4 + high52 r] = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  have ec : wideAdd (wideMul (high52 d7) 68719492368) (ofWord (4503599627370494 &&& d3.1)) =
      wideAdd (ofWord (4503599627370494 &&& d3.1)) (wideMul (high52 d7) 68719492368) :=
    wideAdd_comm _ _
  have hr : r = r3 := by
    simp only [r, ec, r3, squareOut3, wideAddRev_eq, carryPair_eq r2 h2, d3EvenMaskSwap] <;> rfl
  exact congrArg (fun r : Wide => #v[low52 r0, low52 r1, low52 r2, low52 r, low48 d4 + high52 r]) hr

private theorem squareX_eq {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) :
    squareX a = squaredLimbs a := by
  let d3 := squareAcc3 a
  let d4 := squareAcc4 a d3
  let d5 := squareAcc5 a d4
  let d6 := squareAcc6 a d5
  let d7 := squareAcc7 a d6
  let r0 := squareOut0 a d4 d5
  let r1 := squareOut1 a d6 r0
  let r2 := squareOut2 a d7 r1
  have hs : d3.2 >>> 52 = 0 ∧ d4.2 >>> 52 = 0 ∧ d5.2 >>> 52 = 0 ∧ d6.2 >>> 52 = 0 ∧
      r1.2 >>> 52 = 0 ∧ r2.2 >>> 52 = 0 := shiftBounds h
  obtain ⟨h3, h4, h5, h6, h1, h2⟩ := hs
  have e1 := squareXCut1 a
  have e2 := (congrArg (squareX11FC4F a) e1).trans (squareXCut2 a d3 h3)
  have e3 := (congrArg (squareX11FCAB a) e2).trans (squareXCut3 a d3 d4 h4)
  have e4 := (congrArg (squareX11FD1DH a) e3).trans (squareXCut4 a d3 d4 d5 r0 h5)
  have e5 := (congrArg (squareX11FD89 a) e4).trans (squareXCut5 a d3 d4 d6 r0 r1 h6 h1)
  exact (congrArg squareX11FDF2 e5).trans (squareXCut6 d3 d4 d7 r0 r1 r2 h2)

private theorem squareYCut1 (a : Limbs) :
    let d3 := squareAcc3 a
    squareY11F919H a =
      #v[d3.1, d3.2, high52 d3, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
          (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
          (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] := by
  intro d3
  let d := wideAdd (wideMul ((wideMul a[4] a[4]).1 &&& 4503599627370493) 68719492368) (wideDouble (wideAdd (wideMul a[2] a[1]) (wideMul a[3] a[0])))
  change #v[d.1, d.2, high52 d, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] = _
  have hd : d = d3 := by simp only [d, d3, squareAcc3, d3MaskSwap] <;> rfl
  exact congrArg (fun d : Wide => #v[d.1, d.2, high52 d, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
      (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2]) hd

private theorem squareYCut2 (a : Limbs) (d3 : Wide) (h3 : d3.2 >>> 52 = 0) :
    let d4 := squareAcc4 a d3
    squareY11F998 a #v[d3.1, d3.2, high52 d3, (wideMul a[2] a[2]).2, (wideMul a[2] a[2]).1,
        (wideMul (high52 (wideMul a[4] a[4])) 68719492368).2,
        (wideMul (high52 (wideMul a[4] a[4])) 68719492368).1, (wideMul a[4] a[0]).2] =
      #v[d3.1, d4.1, d4.2 >>> 52, high52 d4, (wideMul a[0] a[0]).2, (wideMul a[0] a[0]).1,
          ((BitVec.setWidth 32 (d4.1 >>> 48)).setWidth 64 &&& 15)] := by
  intro d4
  let cross := wideDouble (wideAddRev (wideMul a[3] a[1]) (wideMul a[4] a[0]))
  let sq := wideAdd (wideMul (high52 (wideMul a[4] a[4])) 68719492368) (wideMul a[2] a[2])
  let d := wideAdd (wideAdd sq cross) (carryPair d3)
  change #v[d3.1, d.1, d.2 >>> 52, high52 d, (wideMul a[0] a[0]).2, (wideMul a[0] a[0]).1,
      ((BitVec.setWidth 32 (d.1 >>> 48)).setWidth 64 &&& 15)] = _
  have hd : d = d4 := by
    simp only [d, cross, sq, d4, squareAcc4, wideAddRev_eq, carryPair_eq d3 h3]
  exact congrArg (fun d : Wide => #v[d3.1, d.1, d.2 >>> 52, high52 d, (wideMul a[0] a[0]).2,
      (wideMul a[0] a[0]).1, ((BitVec.setWidth 32 (d.1 >>> 48)).setWidth 64 &&& 15)]) hd

private theorem squareYCut3 (a : Limbs) (d3 d4 : Wide) (h4 : d4.2 >>> 52 = 0) :
    let d5 := squareAcc5 a d4
    let r0 := squareOut0 a d4 d5
    squareY11F9FEH a #v[d3.1, d4.1, d4.2 >>> 52, high52 d4, (wideMul a[0] a[0]).2, (wideMul a[0] a[0]).1,
        ((BitVec.setWidth 32 (d4.1 >>> 48)).setWidth 64 &&& 15)] =
      #v[d3.1, d4.1, d5.2 >>> 52, high52 d5, high52 r0, low52 r0] := by
  intro d5 r0
  let d := wideAdd (wideDouble (wideAddRev (wideMul a[4] a[1]) (wideMul a[3] a[2]))) (carryPair d4)
  let r := wideAdd (wideMul ((d.1 <<< 4 &&& (72057594037927920 : Word) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (d4.1 >>> 48)) &&& 15))) 4294968273) (wideMul a[0] a[0])
  change #v[d3.1, d4.1, d.2 >>> 52, high52 d, high52 r, low52 r] = _
  have hd : d = d5 := by
    simp only [d, d5, squareAcc5, wideAddRev_eq, carryPair_eq d4 h4]
  have hr : r = r0 := by
    simp only [r, r0, squareOut0, hd, combine56_eq] <;> rfl
  exact congrWide (fun d r => #v[d3.1, d4.1, d.2 >>> 52, high52 d, high52 r, low52 r]) hd hr

private theorem squareYCut4 (a : Limbs) (d3 d4 d5 r0 : Wide) (h5 : d5.2 >>> 52 = 0) :
    let d6 := squareAcc6 a d5
    let r1 := squareOut1 a d6 r0
    squareY11FA79 a #v[d3.1, d4.1, d5.2 >>> 52, high52 d5, high52 r0, low52 r0] =
      #v[d3.1, d4.1, low52 r0, a[0] + a[0], a[4] + a[4], d6.2, r1.1, r1.2, high52 d6] := by
  intro d6 r1
  let d := wideAdd (wideAddRev (wideMul (a[4] + a[4]) a[2]) (wideMul a[3] a[3])) (carryPair d5)
  let r := wideAddWordMachine (wideAdd (wideMul (low52 d) 68719492368) (wideMul (a[0] + a[0]) a[1])) (high52 r0)
  change #v[d3.1, d4.1, low52 r0, a[0] + a[0], a[4] + a[4], d.2, r.1, r.2, high52 d] = _
  have hd : d = d6 := by
    simp only [d, d6, squareAcc6, wideAddRev_eq, carryPair_eq d5 h5]
  have hr : r = r1 := by
    simp only [r, r1, squareOut1, hd] <;> rfl
  exact congrWide (fun d r => #v[d3.1, d4.1, low52 r0, a[0] + a[0], a[4] + a[4], d.2, r.1, r.2, high52 d]) hd hr

private theorem squareYCut5 (a : Limbs) (d3 d4 d6 r0 r1 : Wide) (h6 : d6.2 >>> 52 = 0) :
    let d7 := squareAcc7 a d6
    let r2 := squareOut2 a d7 r1
    squareY11FAED a #v[d3.1, d4.1, low52 r0, a[0] + a[0], a[4] + a[4], d6.2, r1.1, r1.2, high52 d6] =
      #v[d3.1, d4.1, low52 r0, r1.2 >>> 52, low52 r1, d7.1, d7.2, (squareOut2Partial a d7).2,
          SquareValue.cf (squareOut2Partial a d7).1 (high52 r1), r2.1] := by
  intro d7 r2
  let d := wideAddRev (wideMul (a[4] + a[4]) a[3]) (carryPair d6)
  let q := wideAdd (wideAdd (wideMul (a[0] + a[0]) a[2]) (wideMul a[1] a[1])) (wideMul (low52 d) 68719492368)
  let r := wideAdd q (carryPair r1)
  change #v[d3.1, d4.1, low52 r0, r1.2 >>> 52, low52 r1, d.1, d.2, q.2, SquareValue.cf q.1 (high52 r1), r.1] = _
  have hd : d = d7 := by
    simp only [d, d7, squareAcc7, wideAddRev_eq, carryPair_eq d6 h6]
  have hq : q = squareOut2Partial a d7 := by
    simp only [q, squareOut2Partial, hd]
  exact congrWide (fun d q => #v[d3.1, d4.1, low52 r0, r1.2 >>> 52, low52 r1, d.1, d.2, q.2,
      SquareValue.cf q.1 (high52 r1), (q.1 + high52 r1)]) hd hq

private theorem squareYCut6 (a : Limbs) (d3 d4 d7 r0 r1 : Wide) (h1 : r1.2 >>> 52 = 0)
    (h2 : (squareOut2 a d7 r1).2 >>> 52 = 0) :
    let r2 := squareOut2 a d7 r1
    let r3 := squareOut3 d3 d7 r2
    squareY11FB56 #v[d3.1, d4.1, low52 r0, r1.2 >>> 52, low52 r1, d7.1, d7.2, (squareOut2Partial a d7).2,
        SquareValue.cf (squareOut2Partial a d7).1 (high52 r1), r2.1] =
      #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3] := by
  intro r2 r3
  change r2.2 >>> 52 = 0 at h2
  let q := squareOut2Partial a d7
  let r2Machine := wideAdd q (carryPair r1)
  let r := wideAdd (wideAddRev (ofWord (d3.1 &&& 4503599627370494)) (wideMul (high52 d7) 68719492368)) (carryPair r2Machine)
  change #v[low52 r0, low52 r1, low52 r2Machine, low52 r,
      low48 d4 + high52 r] = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  have hpair : r2Machine = r2 := by
    simp only [r2Machine, q, r2, squareOut2, carryPair_eq r1 h1]
  have hr : r = r3 := by
    simp only [r, hpair, r3, squareOut3, wideAddRev_eq, carryPair_eq r2 h2, d3EvenMaskSwap] <;> rfl
  exact congrWide (fun r2Machine r => #v[low52 r0, low52 r1, low52 r2Machine, low52 r,
      low48 d4 + high52 r]) hpair hr

private theorem squareY_eq {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) :
    squareY a = squaredLimbs a := by
  let d3 := squareAcc3 a
  let d4 := squareAcc4 a d3
  let d5 := squareAcc5 a d4
  let d6 := squareAcc6 a d5
  let d7 := squareAcc7 a d6
  let r0 := squareOut0 a d4 d5
  let r1 := squareOut1 a d6 r0
  let r2 := squareOut2 a d7 r1
  have hs : d3.2 >>> 52 = 0 ∧ d4.2 >>> 52 = 0 ∧ d5.2 >>> 52 = 0 ∧ d6.2 >>> 52 = 0 ∧
      r1.2 >>> 52 = 0 ∧ r2.2 >>> 52 = 0 := shiftBounds h
  obtain ⟨h3, h4, h5, h6, h1, h2⟩ := hs
  have e1 := squareYCut1 a
  have e2 := (congrArg (squareY11F998 a) e1).trans (squareYCut2 a d3 h3)
  have e3 := (congrArg (squareY11F9FEH a) e2).trans (squareYCut3 a d3 d4 h4)
  have e4 := (congrArg (squareY11FA79 a) e3).trans (squareYCut4 a d3 d4 d5 r0 h5)
  have e5 := (congrArg (squareY11FAED a) e4).trans (squareYCut5 a d3 d4 d6 r0 r1 h6)
  exact (congrArg squareY11FB56 e5).trans (squareYCut6 a d3 d4 d7 r0 r1 h1 h2)

private abbrev addWord (p : Wide) (w : Word) : Wide :=
  (p.1 + w, p.2 + SquareValue.cf p.1 w)

private theorem addWord_eq (p : Wide) (w : Word) :
    addWord p w = wideAdd p (ofWord w) := by
  exact congrArg (fun hi => (p.1 + w, hi + SquareValue.cf p.1 w)) (BitVec.add_zero p.2).symm

private abbrev wordAdd (w : Word) (p : Wide) : Wide :=
  (w + p.1, p.2 + SquareValue.cf w p.1)

private theorem wordAdd_eq (w : Word) (p : Wide) :
    wordAdd w p = wideAdd (ofWord w) p := by
  exact congrArg (fun hi => (w + p.1, hi + SquareValue.cf w p.1)) (BitVec.zero_add p.2).symm

private abbrev mulDoubleLow (a b : Word) : Wide :=
  let p := wideMul (a+a) b
  (p.1, p.2 + (a >>> 63) * b)

private theorem mulDoubleLow_eq (a b : Word) (h : a >>> 63 = 0) :
    mulDoubleLow a b = wideMul (a+a) b := by
  unfold mulDoubleLow
  dsimp only
  rw [h]
  change ((wideMul (a+a) b).1, (wideMul (a+a) b).2 + 0#64 * b) = _
  rw [BitVec.zero_mul, BitVec.add_zero]

private theorem wideAdd_rotate (a b c : Wide) :
    wideAdd (wideAdd a b) c = wideAdd (wideAdd c b) a := by
  calc
    wideAdd (wideAdd a b) c = wideAdd c (wideAdd a b) := wideAdd_comm _ _
    _ = wideAdd c (wideAdd b a) := congrArg (wideAdd c) (wideAdd_comm _ _)
    _ = _ := (wideAdd_assoc _ _ _).symm

private def packSharedSquare (d4 r0 r1 r2 r3 : Wide) : Limbs :=
  #v[low52 r0, low52 r1, low52 r2, 4503599627370495 &&& r3.1,
    (281474976710655 &&& d4.1) + high52 r3]

private theorem packSharedSquare_congr {d4 r0 r1 r2 r3 d4' r0' r1' r2' r3' : Wide}
    (ed4 : d4 = d4') (er0 : r0 = r0') (er1 : r1 = r1') (er2 : r2 = r2') (er3 : r3 = r3') :
    packSharedSquare d4 r0 r1 r2 r3 = packSharedSquare d4' r0' r1' r2' r3' := by
  cases ed4
  cases er0
  cases er1
  cases er2
  cases er3
  rfl

private theorem packSharedSquare_eq (d4 r0 r1 r2 r3 : Wide) :
    packSharedSquare d4 r0 r1 r2 r3 =
      #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3] := by
  simp only [packSharedSquare, low52_swap, low48_swap] <;> rfl

set_option maxHeartbeats 800000 in
private theorem squareWords_eq {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) :
    squareWords a = squaredLimbs a := by
  let d3 := squareAcc3 a
  let d4 := squareAcc4 a d3
  let d5 := squareAcc5 a d4
  let d6 := squareAcc6 a d5
  let d7 := squareAcc7 a d6
  let r0 := squareOut0 a d4 d5
  let r1 := squareOut1 a d6 r0
  let r2 := squareOut2 a d7 r1
  let r3 := squareOut3 d3 d7 r2
  let d4' := addWord (wideAdd
    (wideAdd (wideDouble (wideAddRev (wideMul a[3] a[1]) (wideMul a[4] a[0]))) (wideMul a[2] a[2]))
    (wideMul (high52 (wideMul a[4] a[4])) 68719492368)) (high52 d3)
  let d5' := addWord (wideDouble (wideAddRev (wideMul a[4] a[1]) (wideMul a[3] a[2]))) (high52 d4')
  let d6' := addWord (wideAddRev (wideDouble (wideMul a[2] a[4])) (wideMul a[3] a[3])) (high52 d5')
  let d7' := addWord (wideDouble (wideMul a[3] a[4])) (high52 d6')
  let r0' := squareOut0 a d4' d5'
  let r1' := addWord (wideAdd (wideMul (low52 d6') 68719492368) (mulDoubleLow a[0] a[1])) (high52 r0')
  let r2' := addWord (wideAdd (wideAdd (mulDoubleLow a[0] a[2]) (wideMul a[1] a[1]))
    (wideMul (low52 d7') 68719492368)) (high52 r1')
  let r3' := addWord (wordAdd (4503599627370494 &&& d3.1) (wideMul (high52 d7') 68719492368)) (high52 r2')
  have hwords : squareWords a = packSharedSquare d4' r0' r1' r2' r3' := by
    unfold squareWords squareLimbs
    extract_lets x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44
      x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65
      x66 x67 x68 x69
    let w3 : Wide := (x39, (mulResult x24 68719492368).snd +
      shldResult 1 ((mulResult x8 x5).snd + (mulResult x9 x7).snd + SquareValue.cf x15 x16) x29 +
      SquareValue.cf x33 x38)
    have eq3 : w3 = d3 := rfl
    let hi4 := shldResult 1 ((mulResult x6 x7).snd + (mulResult x9 x5).snd + SquareValue.cf x14 x17) x26 +
      (mulResult x8 x8).snd + SquareValue.cf x36 x12 + (mulResult x32 68719492368).snd +
      SquareValue.cf x41 x40 + SquareValue.cf x43 x44
    let w4 : Wide := (x45, hi4)
    have eq4 : w4 = d4' := by
      change addWord (wideAdd
        (wideAdd (wideDouble (wideAddRev (wideMul a[3] a[1]) (wideMul a[4] a[0]))) (wideMul a[2] a[2]))
        (wideMul (high52 (wideMul a[4] a[4])) 68719492368)) (high52 w3) = _
      simp only [eq3, d4']
    let hi5 := shldResult 1 ((mulResult x9 x8).snd + (mulResult x6 x5).snd + SquareValue.cf x18 x21) x25 +
      SquareValue.cf x35 x46
    let w5 : Wide := (x47, hi5)
    have eq5 : w5 = d5' := by
      change addWord (wideDouble (wideAddRev (wideMul a[4] a[1]) (wideMul a[3] a[2]))) (high52 w4) = _
      simp only [eq4, d5']
    let hi6 := (mulResult x9 x9).snd + shldResult 1 (mulResult x8 x6).snd x10 +
      SquareValue.cf x27 x22 + SquareValue.cf x34 x49
    let w6 : Wide := (x50, hi6)
    have eq6 : w6 = d6' := by
      change addWord (wideAddRev (wideDouble (wideMul a[2] a[4])) (wideMul a[3] a[3])) (high52 w5) = _
      simp only [eq5, d6']
    let w7 : Wide := (x57, shldResult 1 (mulResult x9 x6).snd x11 + SquareValue.cf x31 x56)
    have eq7 : w7 = d7' := by
      change addWord (wideDouble (wideMul a[3] a[4])) (high52 w6) = _
      simp only [eq6, d7']
    let w0 : Wide := (x52, (mulResult x48 4294968273).snd + (mulResult x7 x7).snd + SquareValue.cf x51 x13)
    have er0 : w0 = r0' := by
      change squareOut0 a w4 w5 = _
      simp only [eq4, eq5, r0']
    let hi1 := (mulResult x53 68719492368).snd + ((mulResult x19 x5).snd + x7 >>> 63 * x5) +
      SquareValue.cf x54 x28 + SquareValue.cf x55 x58
    let w1 : Wide := (x59, hi1)
    have er1 : w1 = r1' := by
      change addWord (wideAdd (wideMul (low52 w6) 68719492368) (mulDoubleLow a[0] a[1])) (high52 w0) = _
      simp only [eq6, er0, r1']
    let hi2 := (mulResult x19 x8).snd + x7 >>> 63 * x8 + (mulResult x5 x5).snd +
      SquareValue.cf x30 x23 + (mulResult x60 68719492368).snd + SquareValue.cf x37 x61 +
      SquareValue.cf x62 x64
    let w2 : Wide := (x66, hi2)
    have er2 : w2 = r2' := by
      change addWord (wideAdd (wideAdd (mulDoubleLow a[0] a[2]) (wideMul a[1] a[1]))
        (wideMul (low52 w7) 68719492368)) (high52 w1) = _
      simp only [eq7, er1, r2']
    let hi3 := (mulResult x63 68719492368).snd + SquareValue.cf x42 x65 + SquareValue.cf x67 x68
    let wlast : Wide := (x69, hi3)
    have er3 : wlast = r3' := by
      change addWord (wordAdd (4503599627370494 &&& w3.1) (wideMul (high52 w7) 68719492368)) (high52 w2) = _
      simp only [eq3, eq7, er2, r3']
    change packSharedSquare w4 w0 w1 w2 wlast = _
    exact packSharedSquare_congr eq4 er0 er1 er2 er3
  have h0 : a[0] >>> 63 = 0 := limbShiftZero _ (limbBound h 0)
  have h4nat : a[4].toNat ≤ 2^56 - 1 := (limbBound h 4).le
  have h2nat : a[2].toNat ≤ 2^56 - 1 := (limbBound h 2).le
  have h3nat : a[3].toNat ≤ 2^56 - 1 := (limbBound h 3).le
  have hd42 : wideDouble (wideMul a[2] a[4]) = wideMul (a[4]+a[4]) a[2] :=
    (mulDouble _ _ (by omega)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul h4nat h2nat)) (by decide))).symm
  have hd43 : wideDouble (wideMul a[3] a[4]) = wideMul (a[4]+a[4]) a[3] :=
    (mulDouble _ _ (by omega)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul h4nat h3nat)) (by decide))).symm
  have e4 : d4' = d4 := by
    let c := wideDouble (wideAdd (wideMul a[3] a[1]) (wideMul a[4] a[0]))
    let p := wideMul a[2] a[2]
    let scaled := wideMul (high52 (wideMul a[4] a[4])) 68719492368
    let carry := ofWord (high52 d3)
    calc
      d4' = wideAdd (wideAdd (wideAdd c p) scaled) carry := by
        simp only [d4', c, p, scaled, carry, addWord_eq, wideAddRev_eq]
      _ = d4 := congrArg (fun q => wideAdd q carry) (wideAdd_rotate c p scaled)
  have e5 : d5' = d5 := by
    simp only [d5', d5, squareAcc5, addWord_eq, e4, wideAddRev_eq]
  have e6 : d6' = d6 := by
    simp only [d6', d6, squareAcc6, e5, addWord_eq, hd42, wideAddRev_eq]
  have e7 : d7' = d7 := by
    simp only [d7', d7, squareAcc7, e6, hd43, addWord_eq]
  have e0 : r0' = r0 := by rw [show r0' = squareOut0 a d4' d5' from rfl, e4, e5]
  have e1 : r1' = r1 := by
    simp only [r1', r1, squareOut1, addWord_eq, e6, e0, mulDoubleLow_eq _ _ h0]
  have e2 : r2' = r2 := by
    simp only [r2', r2, squareOut2, squareOut2Partial, addWord_eq, e7, e1, mulDoubleLow_eq _ _ h0]
  have e3 : r3' = r3 := by
    simp only [r3', r3, squareOut3, addWord_eq, wordAdd_eq, e7, e2]
  exact hwords.trans ((packSharedSquare_congr e4 e0 e1 e2 e3).trans (packSharedSquare_eq d4 r0 r1 r2 r3))

theorem squareX_repr (a : Limbs) (x : Fin modulus) (h : FieldRepr a x 8) :
    FieldRepr (squareX a) (x * x) 1 := by
  rw [squareX_eq h, ← squareWords_eq h]
  exact squareWords_repr a x h

theorem squareY_repr (a : Limbs) (x : Fin modulus) (h : FieldRepr a x 8) :
    FieldRepr (squareY a) (x * x) 1 := by
  rw [squareY_eq h, ← squareWords_eq h]
  exact squareWords_repr a x h

end K256.Proofs.Sec1.Affine.Uncompressed
