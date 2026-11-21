import K256.Proofs.Ecdh.Multiply.Endomorphism.Words

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism

open K256.Proofs.Common.Field
open K256.Proofs.Common.Field.Multiply
open K256.Proofs.Common.Field.Multiply.SqrtSchedule
  (Coefficients reduceWords productCoefficients reduce_productCoefficients
    wideAddRev_eq wideAdd_left_comm wideAdd_comm)

private theorem betaTop_mask (u : Word) :
    (0xffffffffffffc : Word) &&& (wideMul u betaLimbs[(4 : Fin 5)]).1 =
      low52 (wideMul u betaLimbs[(4 : Fin 5)]) := by
  have hmod : (u * betaLimbs[(4 : Fin 5)]).toNat % 4 = 0 := by
    rw [BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2^64), Nat.mul_mod]
    rw [show betaLimbs[(4 : Fin 5)].toNat % 4 = 0 by decide +kernel, Nat.mul_zero, Nat.zero_mod]
  have hbits : (u * betaLimbs[(4 : Fin 5)]) &&& 3 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    exact (Nat.and_two_pow_sub_one_eq_mod _ 2).trans hmod
  exact SquareValue.hole _ _ 3 _ hbits (by decide +kernel)

private theorem carry52_eq {q : Wide} {x A : Nat} (h : BoundedValue (wideValue q) x A)
    (hA : A < 2^116 := by decide) : (high52 q, q.2 >>> 52) = ofWord (high52 q) := by
  refine Prod.ext rfl (BitVec.eq_of_toNat_eq ?_)
  have hv := Nat.lt_of_le_of_lt h.le hA
  rw [← h.eq] at hv
  change q.1.toNat + 2^64 * q.2.toNat < 2^116 at hv
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change q.2.toNat / 2^52 = 0
  omega

private def betaCoefficients (p : Fin 5 → Fin 5 → Wide) : Coefficients :=
  ⟨p 0 0,
   wideAdd (p 1 0) (p 0 1),
   wideAdd (wideAdd (p 1 1) (p 0 2)) (p 2 0),
   wideAdd (p 3 0) (wideAdd (p 2 1) (wideAdd (p 1 2) (p 0 3))),
   wideAdd (wideAdd (wideAdd (wideAdd (p 1 3) (p 0 4)) (p 2 2)) (p 3 1)) (p 4 0),
   wideAddRev (p 4 1) (wideAdd (wideAdd (p 2 3) (p 1 4)) (p 3 2)),
   wideAddRev (p 4 2) (wideAdd (p 3 3) (p 2 4)),
   wideAddRev (p 4 3) (p 3 4), p 4 4⟩

private theorem betaCoefficients_eq (p : Fin 5 → Fin 5 → Wide) :
    betaCoefficients p = productCoefficients p := by
  simp only [betaCoefficients, productCoefficients, wideAddRev_eq,
    wideAdd_left_comm, wideAdd_comm]

private def betaFinish (c : Coefficients) (d₃ d₄ r₀ d₆ : Wide)
    (carry₀ carry₆ : Wide) (mask₃ mask₄ : Wide → Word) : Limbs :=
  let r₁ := wideAdd (wideAdd c.c1 (wideMul (low52 d₆) 0x1000003d10)) carry₀
  let d₇ := wideAdd c.c7 carry₆
  let r₂ := wideAdd (wideAdd c.c2 (wideMul (low52 d₇) 0x1000003d10)) (ofWord (high52 r₁))
  let r₃ := wideAdd (wideAddRev (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10))
    (ofWord (high52 r₂))
  #v[low52 r₀, low52 r₁, low52 r₂, mask₃ r₃, mask₄ d₄ + high52 r₃]

private def betaReduce (c : Coefficients) (d₃ : Wide) : Limbs :=
  let d₄ := wideAdd (wideAdd c.c4 (wideMul (high52 c.c8) 0x1000003d10)) (ofWord (high52 d₃))
  let d₅ := wideAdd c.c5 (ofWord (high52 d₄))
  let r₀ := wideAdd (wideMul (combine56 d₅ d₄) 0x1000003d1) c.c0
  let d₆ := wideAdd c.c6 (ofWord (high52 d₅))
  betaFinish c d₃ d₄ r₀ d₆ (high52 r₀, r₀.2 >>> 52) (high52 d₆, d₆.2 >>> 52)
    (fun q => 0xfffffffffffff &&& q.1) (fun q => 0xffffffffffff &&& q.1)

private theorem betaReduce_eq (c : Coefficients)
    (hmask : (0xffffffffffffc : Word) &&& c.c8.1 = low52 c.c8)
    (hc₀ : BoundedValue (wideValue c.c0) (wideValue c.c0) (2^105))
    (hc₃ : BoundedValue (wideValue c.c3) (wideValue c.c3) (4 * 2^105))
    (hc₄ : BoundedValue (wideValue c.c4) (wideValue c.c4) (5 * 2^105))
    (hc₅ : BoundedValue (wideValue c.c5) (wideValue c.c5) (4 * 2^105))
    (hc₆ : BoundedValue (wideValue c.c6) (wideValue c.c6) (3 * 2^105))
    (hc₈ : BoundedValue (wideValue c.c8) (wideValue c.c8) (2^105)) :
    betaReduce c (wideAdd (wideMul (0xffffffffffffc &&& c.c8.1) 0x1000003d10) c.c3) =
      reduceWords wideAdd wideAdd wideAdd wideAddRev c
        (wideMul (high52 c.c8) 0x1000003d10) := by
  have hR : BoundedValue (0x1000003d10 : Word).toNat 0x1000003d10 0x1000003d10 :=
    ⟨rfl, Nat.le_refl _⟩
  have hr : BoundedValue (0x1000003d1 : Word).toNat 0x1000003d1 0x1000003d1 :=
    ⟨rfl, Nat.le_refl _⟩
  let d₃ := wideAdd c.c3 (wideMul (low52 c.c8) 0x1000003d10)
  have e₃ : wideAdd (wideMul (0xffffffffffffc &&& c.c8.1) 0x1000003d10) c.c3 = d₃ := by
    exact (congrArg (fun w => wideAdd (wideMul w 0x1000003d10) c.c3) hmask).trans
      (wideAdd_comm _ _)
  refine (congrArg (betaReduce c) e₃).trans ?_
  let d₄ := wideAdd (wideAdd c.c4 (wideMul (high52 c.c8) 0x1000003d10)) (ofWord (high52 d₃))
  let d₅ := wideAdd c.c5 (ofWord (high52 d₄))
  let r₀ := wideAdd (wideMul (combine56 d₅ d₄) 0x1000003d1) c.c0
  let d₆ := wideAdd c.c6 (ofWord (high52 d₅))
  have hd₃ := hc₃.wideAdd (hc₈.low52.wideMul hR)
  have hd₄ := (hc₄.wideAdd (hc₈.high52.wideMul hR)).wideAdd hd₃.high52.ofWord
  have hd₅ := hc₅.wideAdd hd₄.high52.ofWord
  have hr₀ := ((hd₅.combine56 hd₄).wideMul hr).wideAdd hc₀
  have hd₆ := hc₆.wideAdd hd₅.high52.ofWord
  have e₀ : (high52 r₀, r₀.2 >>> 52) = ofWord (high52 r₀) := carry52_eq hr₀
  have e₆ : (high52 d₆, d₆.2 >>> 52) = ofWord (high52 d₆) := carry52_eq hd₆
  have em₃ : (fun q : Wide => 0xfffffffffffff &&& q.1) = low52 :=
    funext fun q => BitVec.and_comm _ _
  have em₄ : (fun q : Wide => 0xffffffffffff &&& q.1) = low48 :=
    funext fun q => BitVec.and_comm _ _
  have hfinish := congr (congr (congr (congrArg (betaFinish c d₃ d₄ r₀ d₆) e₀) e₆) em₃) em₄
  exact hfinish

theorem betaMulWords_eq (a : Limbs) {x : Fin modulus} (ha : FieldRepr a x 1) :
    betaMulWords a = mulWords a betaLimbs := by
  have hlimb (i : Fin 5) : BoundedValue a[i].toNat a[i].toNat (2 * (2^52 - 1)) := by
    refine ⟨rfl, ?_⟩
    have hi : (if i.val < 4 then a[i].toNat ≤ 2 * (2^52 - 1)
        else a[i].toNat ≤ 2 * (2^48 - 1)) :=
      by simpa only [getElem!_pos, i.isLt] using ha.1 i
    split at hi <;> omega
  have hbeta : ∀ j : Fin 5, betaLimbs[j].toNat ≤ 2^52 - 1 := by decide +kernel
  let p (i j : Fin 5) := wideMul a[i] betaLimbs[j]
  have hp (i j : Fin 5) : BoundedValue (wideValue (p i j)) (wideValue (p i j)) (2^105) := by
    have hb : BoundedValue betaLimbs[j].toNat betaLimbs[j].toNat (2^52 - 1) := ⟨rfl, hbeta j⟩
    have h := (hlimb i).wideMul hb
    exact ⟨rfl, h.eq ▸ Nat.le_trans h.le (by decide)⟩
  let c := betaCoefficients p
  have hc₃ := (hp 3 0).wideAdd ((hp 2 1).wideAdd ((hp 1 2).wideAdd (hp 0 3)))
  have hc₄ := ((((hp 1 3).wideAdd (hp 0 4)).wideAdd (hp 2 2)).wideAdd (hp 3 1)).wideAdd (hp 4 0)
  have hc₅ := (hp 4 1).wideAddRev (((hp 2 3).wideAdd (hp 1 4)).wideAdd (hp 3 2))
  have hc₆ := (hp 4 2).wideAddRev ((hp 3 3).wideAdd (hp 2 4))
  have hreduce := betaReduce_eq c (betaTop_mask a[(4 : Fin 5)]) (hp 0 0)
    ⟨rfl, hc₃.eq ▸ hc₃.le⟩ ⟨rfl, hc₄.eq ▸ hc₄.le⟩ ⟨rfl, hc₅.eq ▸ hc₅.le⟩
    ⟨rfl, hc₆.eq ▸ hc₆.le⟩ (hp 4 4)
  exact hreduce.trans ((congrArg
    (fun coeff => reduceWords wideAdd wideAdd wideAdd wideAddRev coeff
      (wideMul (high52 coeff.c8) 0x1000003d10)) (betaCoefficients_eq p)).trans
    (reduce_productCoefficients betaLimbs a))

end K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
