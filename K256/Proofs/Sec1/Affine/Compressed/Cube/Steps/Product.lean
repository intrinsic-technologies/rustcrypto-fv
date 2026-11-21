import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Words
import K256.Proofs.Common.Field.Multiply
import K256.Proofs.Common.Field.Multiply.SqrtSchedule.High
import K256.Proofs.Sec1.Tactic.Words

namespace K256.Proofs.Sec1.Affine.Compressed

open X86Proofs Common.Field Common.Field.Multiply Common.Field.Multiply.SqrtSchedule

private def carry52 (a : Wide) : Wide := (high52 a, a.2 >>> 52)

private def combineNibbles (a b : Wide) : Word :=
  a.1 <<< 4 &&& (72057594037927920 : Word) |||
    (BitVec.setWidth 32 (b.1 >>> 48)).setWidth 64 &&& 15

private def scaleCarry (q : Wide) : Wide :=
  let p := wideMul (shrdResult 52 q.1 q.2) 0x1000003d10
  (p.1, p.2 + (q.2 >>> 52) * 0x1000003d10)

private def wideAddLow (a : Word) (b : Wide) : Wide :=
  (a + b.1, b.2 + BitVec.ofNat 64 (addSpec a b.1).2.CF.toNat)

private def low52Rev (q : Wide) : Word := (0xfffffffffffff : Word) &&& q.1

private def finishProduct (c₀ c₁ c₂ d₃ c₄ c₅ c₆ c₇ c₈ : Wide) : Limbs :=
  let d₄ := wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10)) (carry52 d₃)
  let d₅ := wideAdd c₅ (carry52 d₄)
  let r₀ := wideAdd (wideMul (combineNibbles d₅ d₄) 0x1000003d1) c₀
  let d₆ := wideAdd c₆ (carry52 d₅)
  let r₁ := wideAdd (wideAdd c₁ (wideMul (low52 d₆) 0x1000003d10)) (ofWord (high52 r₀))
  let d₇ := wideAdd c₇ (carry52 d₆)
  let r₂ := wideAdd (wideAdd c₂ (wideMul (low52 d₇) 0x1000003d10)) (carry52 r₁)
  let r₃ := wideAdd (wideAddLow (low52 d₃) (scaleCarry d₇)) (carry52 r₂)
  #v[low52 r₀, low52 r₁, low52 r₂, low52Rev r₃, low48 d₄ + high52 r₃]

private def productSchedule (p : Fin 5 → Fin 5 → Wide) : Limbs :=
  let c₈ := p 4 4
  let c₃ := wideAdd (p 3 0) (wideAdd (p 2 1) (wideAdd (p 1 2) (p 0 3)))
  let d₃ := wideAdd (wideMul (low52 c₈) 0x1000003d10) c₃
  let c₄ := wideAdd (wideAdd (wideAdd (wideAdd (p 1 3) (p 0 4)) (p 2 2)) (p 3 1)) (p 4 0)
  let c₅ := wideAddRev (p 4 1) (wideAdd (wideAdd (p 2 3) (p 1 4)) (p 3 2))
  let c₆ := wideAddRev (p 4 2) (wideAdd (p 3 3) (p 2 4))
  let c₁ := wideAdd (p 1 0) (p 0 1)
  let c₇ := wideAdd (p 4 3) (p 3 4)
  let c₂ := wideAdd (wideAdd (p 1 1) (p 0 2)) (p 2 0)
  finishProduct (p 0 0) c₁ c₂ d₃ c₄ c₅ c₆ c₇ c₈

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4096 in
private theorem cubeProduct_eq_schedule (a b : Limbs) :
    cubeProduct a b = productSchedule (fun i j => wideMul b[i] a[j]) := by
  apply Vector.ext
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  all_goals kernel_refl

private theorem combineNibbles_eq (a b : Wide) : combineNibbles a b = combine56 a b := by
  rw [combineNibbles, combine56, BitVec.setWidth_and]
  rfl

private theorem highWord_shift_eq_zero {q : Wide} {x A : Nat} (h : BoundedValue (wideValue q) x A)
    (hA : A < 2^116 := by decide) : q.2 >>> 52 = 0 := by
  apply BitVec.eq_of_toNat_eq
  have hv := Nat.lt_of_le_of_lt h.le hA
  rw [← h.eq] at hv
  change q.1.toNat + 2^64 * q.2.toNat < 2^116 at hv
  change (q.2 >>> 52).toNat = 0
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem carry52_eq {q : Wide} {x A : Nat} (h : BoundedValue (wideValue q) x A)
    (hA : A < 2^116 := by decide) : carry52 q = ofWord (high52 q) :=
  Prod.ext rfl (highWord_shift_eq_zero h hA)

private theorem scaleCarry_eq {q : Wide} {x A : Nat} (h : BoundedValue (wideValue q) x A)
    (hA : A < 2^116 := by decide) : scaleCarry q = wideMul (high52 q) 0x1000003d10 := by
  have hzero := highWord_shift_eq_zero h hA
  rw [scaleCarry, shrd52_eq]
  refine Prod.ext rfl ?_
  change (wideMul (high52 q) 0x1000003d10).2 + (q.2 >>> 52) * 0x1000003d10 = _
  rw [hzero]
  exact BitVec.add_zero _

private theorem wideAddLow_eq (a : Word) (b : Wide) :
    wideAddLow a b = wideAddRev (ofWord a) b := by
  refine Prod.ext rfl ?_
  exact (congrArg (· + BitVec.ofNat 64 (addSpec a b.1).2.CF.toNat) (BitVec.add_zero b.2)).symm

private theorem low52Rev_eq (q : Wide) : low52Rev q = low52 q :=
  BitVec.and_comm _ _

private theorem limbBound {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) (i : Fin 5) :
    BoundedValue a[i].toNat a[i].toNat (if i.val < 4 then 16 * (2^52-1) else 16 * (2^48-1)) := by
  refine ⟨rfl, ?_⟩
  have hi := h.1 i
  split <;> rename_i he <;> simpa only [he, ite_true, ite_false, getElem!_pos, i.isLt] using hi

private def orderedSchedule (p : Fin 5 → Fin 5 → Wide) : Limbs :=
  let c₈ := p 4 4
  let d₃ := wideAdd (wideAdd (wideAdd (wideAdd (p 0 3) (p 1 2)) (p 2 1)) (p 3 0))
    (wideMul (low52 c₈) 0x1000003d10)
  let c₄ := wideAdd (wideAdd (wideAdd (wideAdd (p 0 4) (p 1 3)) (p 2 2)) (p 3 1)) (p 4 0)
  let c₅ := wideAdd (wideAdd (wideAddRev (p 1 4) (p 2 3)) (p 3 2)) (p 4 1)
  let c₆ := wideAdd (wideAddRev (p 2 4) (p 3 3)) (p 4 2)
  let c₁ := wideAdd (p 0 1) (p 1 0)
  let c₇ := wideAddRev (p 3 4) (p 4 3)
  let c₂ := wideAdd (wideAdd (p 0 2) (p 1 1)) (p 2 0)
  finishProduct (p 0 0) c₁ c₂ d₃ c₄ c₅ c₆ c₇ c₈

private theorem productSchedule_eq_ordered (p : Fin 5 → Fin 5 → Wide) :
    productSchedule p = orderedSchedule p := by
  dsimp only [productSchedule, orderedSchedule]
  rw [wideAdd_comm (p 1 0) (p 0 1), wideAdd_comm (p 1 1) (p 0 2),
    wideAdd_comm (p 1 2) (p 0 3), wideAdd_comm (p 2 1), wideAdd_comm (p 3 0),
    wideAdd_comm (wideMul (low52 (p 4 4)) 0x1000003d10), wideAdd_comm (p 1 3) (p 0 4),
    wideAddRev_eq (p 4 1), wideAdd_comm (p 4 1), wideAdd_comm (p 2 3) (p 1 4),
    wideAddRev_eq (p 1 4), wideAddRev_eq (p 4 2), wideAdd_comm (p 4 2),
    wideAdd_comm (p 3 3) (p 2 4), wideAddRev_eq (p 2 4),
    wideAdd_comm (p 4 3) (p 3 4), wideAddRev_eq (p 3 4)]

set_option maxHeartbeats 450000 in
set_option maxRecDepth 4096 in
private theorem finishProduct_eq {c₀ c₁ c₂ d₃ c₄ c₅ c₆ c₇ c₈ : Wide} :
    let d₄ := wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10)) (ofWord (high52 d₃))
    let d₅ := wideAdd c₅ (ofWord (high52 d₄))
    let r₀ := wideAdd (wideMul (combine56 d₅ d₄) 0x1000003d1) c₀
    let d₆ := wideAdd c₆ (ofWord (high52 d₅))
    let r₁ := wideAdd (wideAdd c₁ (wideMul (low52 d₆) 0x1000003d10)) (ofWord (high52 r₀))
    let d₇ := wideAdd c₇ (ofWord (high52 d₆))
    let r₂ := wideAdd (wideAdd c₂ (wideMul (low52 d₇) 0x1000003d10)) (ofWord (high52 r₁))
    let r₃ := wideAdd (wideAddRev (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10))
      (ofWord (high52 r₂))
    carry52 d₃ = ofWord (high52 d₃) →
    carry52 d₄ = ofWord (high52 d₄) →
    carry52 d₅ = ofWord (high52 d₅) →
    carry52 d₆ = ofWord (high52 d₆) →
    scaleCarry d₇ = wideMul (high52 d₇) 0x1000003d10 →
    carry52 r₁ = ofWord (high52 r₁) →
    carry52 r₂ = ofWord (high52 r₂) →
    finishProduct c₀ c₁ c₂ d₃ c₄ c₅ c₆ c₇ c₈ =
      #v[low52 r₀, low52 r₁, low52 r₂, low52 r₃, low48 d₄ + high52 r₃] := by
  intro d₄ d₅ r₀ d₆ r₁ d₇ r₂ r₃ eq₃ eq₄ eq₅ eq₆ eq₇ eq₁ eq₂
  let D₄ := wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10)) (carry52 d₃)
  have eD₄ : D₄ = d₄ := congrArg (wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10))) eq₃
  let D₅ := wideAdd c₅ (carry52 D₄)
  have eD₅ : D₅ = d₅ := congrArg (wideAdd c₅) ((congrArg carry52 eD₄).trans eq₄)
  let R₀ := wideAdd (wideMul (combineNibbles D₅ D₄) 0x1000003d1) c₀
  have eR₀ : R₀ = r₀ :=
    (congrArg (fun t => wideAdd (wideMul t 0x1000003d1) c₀)
      ((congrArg (fun t => combineNibbles t D₄) eD₅).trans
        ((congrArg (combineNibbles d₅) eD₄).trans (combineNibbles_eq d₅ d₄))))
  let D₆ := wideAdd c₆ (carry52 D₅)
  have eD₆ : D₆ = d₆ := congrArg (wideAdd c₆) ((congrArg carry52 eD₅).trans eq₅)
  let R₁ := wideAdd (wideAdd c₁ (wideMul (low52 D₆) 0x1000003d10)) (ofWord (high52 R₀))
  have eR₁ : R₁ = r₁ :=
    (congrArg (fun t => wideAdd (wideAdd c₁ (wideMul (low52 t) 0x1000003d10)) (ofWord (high52 R₀))) eD₆).trans
      (congrArg (fun t => wideAdd (wideAdd c₁ (wideMul (low52 d₆) 0x1000003d10)) (ofWord (high52 t))) eR₀)
  let D₇ := wideAdd c₇ (carry52 D₆)
  have eD₇ : D₇ = d₇ := congrArg (wideAdd c₇) ((congrArg carry52 eD₆).trans eq₆)
  let R₂ := wideAdd (wideAdd c₂ (wideMul (low52 D₇) 0x1000003d10)) (carry52 R₁)
  have eR₂ : R₂ = r₂ :=
    (congrArg (fun t => wideAdd (wideAdd c₂ (wideMul (low52 t) 0x1000003d10)) (carry52 R₁)) eD₇).trans
    (congrArg (wideAdd (wideAdd c₂ (wideMul (low52 d₇) 0x1000003d10))) ((congrArg carry52 eR₁).trans eq₁))
  let R₃ := wideAdd (wideAddLow (low52 d₃) (scaleCarry D₇)) (carry52 R₂)
  have eR₃ : R₃ = r₃ :=
    (congrArg (fun t => wideAdd (wideAddLow (low52 d₃) t) (carry52 R₂))
      ((congrArg scaleCarry eD₇).trans eq₇)).trans
    ((congrArg (fun t => wideAdd t (carry52 R₂)) (wideAddLow_eq _ _)).trans
      (congrArg (wideAdd (wideAddRev (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10)))
        ((congrArg carry52 eR₂).trans eq₂)))
  change #v[low52 R₀, low52 R₁, low52 R₂, low52Rev R₃, low48 D₄ + high52 R₃] = _
  rw [eR₀, eR₁, eR₂, eR₃, eD₄, low52Rev_eq]

set_option maxHeartbeats 900000 in
set_option maxRecDepth 4096 in
private theorem orderedSchedule_eq_mulWords {a b : Limbs} {x y : Fin modulus}
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    orderedSchedule (fun i j => wideMul b[i] a[j]) = mulWords b a := by
  let hp (i j : Fin 5) := (limbBound hb i).wideMul (limbBound ha j)
  have hR : BoundedValue (0x1000003d10 : Word).toNat 0x1000003d10 0x1000003d10 := ⟨rfl, Nat.le_refl _⟩
  have hr : BoundedValue (0x1000003d1 : Word).toNat 0x1000003d1 0x1000003d1 := ⟨rfl, Nat.le_refl _⟩
  have hc₈ := hp 4 4
  have hc₃ := (((hp 0 3).wideAdd (hp 1 2)).wideAdd (hp 2 1)).wideAdd (hp 3 0)
  have hd₃ := hc₃.wideAdd (hc₈.low52.wideMul hR)
  have hc₄ := ((((hp 0 4).wideAdd (hp 1 3)).wideAdd (hp 2 2)).wideAdd (hp 3 1)).wideAdd (hp 4 0)
  have hd₄ := (hc₄.wideAdd (hc₈.high52.wideMul hR)).wideAdd hd₃.high52.ofWord
  have hc₅ := (((hp 1 4).wideAddRev (hp 2 3)).wideAdd (hp 3 2)).wideAdd (hp 4 1)
  have hd₅ := hc₅.wideAdd hd₄.high52.ofWord
  have hr₀ := ((hd₅.combine56 hd₄).wideMul hr).wideAdd (hp 0 0)
  have hc₆ := ((hp 2 4).wideAddRev (hp 3 3)).wideAdd (hp 4 2)
  have hd₆ := hc₆.wideAdd hd₅.high52.ofWord
  have hc₁ := (hp 0 1).wideAdd (hp 1 0)
  have hr₁ := (hc₁.wideAdd (hd₆.low52.wideMul hR)).wideAdd hr₀.high52.ofWord
  have hc₇ := (hp 3 4).wideAddRev (hp 4 3)
  have hd₇ := hc₇.wideAdd hd₆.high52.ofWord
  have hc₂ := ((hp 0 2).wideAdd (hp 1 1)).wideAdd (hp 2 0)
  have hr₂ := (hc₂.wideAdd (hd₇.low52.wideMul hR)).wideAdd hr₁.high52.ofWord
  have eq₃ := carry52_eq hd₃
  have eq₄ := carry52_eq hd₄
  have eq₅ := carry52_eq hd₅
  have eq₆ := carry52_eq hd₆
  have eq₇ := scaleCarry_eq hd₇
  have eq₁ := carry52_eq hr₁
  have eq₂ := carry52_eq hr₂
  exact finishProduct_eq eq₃ eq₄ eq₅ eq₆ eq₇ eq₁ eq₂

theorem cubeProduct_repr (a b : Limbs) (x y : Fin modulus)
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    FieldRepr (cubeProduct a b) (x * y) 1 := by
  have eq := (cubeProduct_eq_schedule a b).trans
    ((productSchedule_eq_ordered _).trans (orderedSchedule_eq_mulWords ha hb))
  exact eq.symm ▸ (Fin.mul_comm y x) ▸ mulWords_repr b a y x hb ha

end K256.Proofs.Sec1.Affine.Compressed
