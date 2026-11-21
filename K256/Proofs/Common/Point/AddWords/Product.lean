import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Commutative

namespace K256.Proofs.Common.Point.AddWords.Product

open Field Field.Multiply Field.Multiply.SqrtSchedule X86Proofs

inductive Schedule where
  | diagonal | reverseCarry | fullCarry | xRight | yLeft | yRight

def shiftWide (w : Wide) : Wide := (high52 w, w.2 >>> 52)

def scaleWide (w : Wide) : Wide := scaleHigh w (shrdResult 52 w.1 w.2)

def c8 (s : Schedule) (a b : Limbs) : Wide :=
  match s with
  | .diagonal | .reverseCarry | .fullCarry =>
    wideMul a[4] b[4]
  | .xRight | .yLeft | .yRight =>
    wideMul b[4] a[4]

def d3 (s : Schedule) (a b : Limbs) (c8 : Wide) : Wide :=
  match s with
  | .diagonal | .fullCarry =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0] b[3]) (wideMul a[1] b[2])) (wideMul a[2] b[1])) (wideMul
        a[3] b[0])) (wideMul (low52 c8) 0x1000003d10)
  | .reverseCarry =>
    wideAddRev (wideMul (low52 c8) 0x1000003d10) (wideAdd (wideAdd (wideAdd (wideMul a[0] b[3]) (wideMul a[1]
        b[2])) (wideMul a[2] b[1])) (wideMul a[3] b[0]))
  | .xRight =>
    wideAdd (wideMul (low52 c8) 0x1000003d10) (wideAdd (wideMul b[3] a[0]) (wideAdd (wideMul b[2] a[1])
        (wideAdd (wideMul b[1] a[2]) (wideMul b[0] a[3]))))
  | .yLeft =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[2] a[1]) (wideMul a[2] b[1])) (wideMul a[3] b[0])) (wideMul
        b[3] a[0])) (wideMul (low52 c8) 0x1000003d10)
  | .yRight =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[2] a[1]) (wideMul b[1] a[2])) (wideMul a[3] b[0])) (wideMul
        b[3] a[0])) (wideMul (low52 c8) 0x1000003d10)

def d4 (s : Schedule) (a b : Limbs) (c8 d3 : Wide) : Wide :=
  match s with
  | .diagonal =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0] b[4]) (wideMul a[1] b[3])) (wideMul
        a[2] b[2])) (wideMul a[3] b[1])) (wideMul a[4] b[0])) (wideMul (high52 c8) 0x1000003d10)) (ofWord
        (high52 d3))
  | .reverseCarry =>
    wideAdd (wideAddRev (wideMul (high52 c8) 0x1000003d10) (wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0]
        b[4]) (wideMul a[1] b[3])) (wideMul a[2] b[2])) (wideMul a[3] b[1])) (wideMul a[4] b[0]))) (ofWord
        (high52 d3))
  | .fullCarry =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0] b[4]) (wideMul a[1] b[3])) (wideMul
        a[2] b[2])) (wideMul a[3] b[1])) (wideMul a[4] b[0])) (scaleWide c8)) (shiftWide d3)
  | .xRight =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[3]) (wideMul b[0] a[4])) (wideMul
        b[2] a[2])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) (wideMul (high52 c8) 0x1000003d10)) (shiftWide
        d3)
  | .yLeft =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[2] a[2]) (wideMul a[3] b[1])) (wideMul
        b[3] a[1])) (wideMul a[4] b[0])) (wideMul b[4] a[0])) (scaleWide c8)) (shiftWide d3)
  | .yRight =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[2] a[2]) (wideMul a[3] b[1])) (wideMul
        a[4] b[0])) (wideMul b[3] a[1])) (wideMul b[4] a[0])) (wideMul (high52 c8) 0x1000003d10)) (shiftWide
        d3)

def d5 (s : Schedule) (a b : Limbs) (d4 : Wide) : Wide :=
  match s with
  | .diagonal | .reverseCarry =>
    wideAdd (wideAdd (wideAdd (wideAddRev (wideMul a[1] b[4]) (wideMul a[2] b[3])) (wideMul a[3] b[2]))
        (wideMul a[4] b[1])) (ofWord (high52 d4))
  | .fullCarry =>
    wideAdd (wideAdd (wideAdd (wideAddRev (wideMul a[1] b[4]) (wideMul a[2] b[3])) (wideMul a[3] b[2]))
        (wideMul a[4] b[1])) (shiftWide d4)
  | .xRight =>
    wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[2] a[3]) (wideMul b[1] a[4]))
        (wideMul b[3] a[2]))) (shiftWide d4)
  | .yLeft =>
    wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul b[3] a[2]) (wideMul a[3] b[2]))
        (wideMul a[4] b[1]))) (shiftWide d4)
  | .yRight =>
    wideAdd (wideAddRev (wideMul b[4] a[1]) (wideAdd (wideAdd (wideMul a[3] b[2]) (wideMul a[4] b[1]))
        (wideMul b[3] a[2]))) (shiftWide d4)

def r0 (s : Schedule) (a b : Limbs) (d4 d5 : Wide) : Wide :=
  match s with
  | .diagonal | .fullCarry =>
    wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul a[0] b[0])
  | .reverseCarry =>
    wideAddRev (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul a[0] b[0])
  | .xRight | .yLeft | .yRight =>
    wideAdd (wideMul (combine56 d5 d4) 0x1000003d1) (wideMul b[0] a[0])

def d6 (s : Schedule) (a b : Limbs) (d5 : Wide) : Wide :=
  match s with
  | .diagonal | .reverseCarry =>
    wideAdd (wideAdd (wideAddRev (wideMul a[2] b[4]) (wideMul a[3] b[3])) (wideMul a[4] b[2])) (ofWord (high52 d5))
  | .fullCarry =>
    wideAdd (wideAdd (wideAddRev (wideMul a[2] b[4]) (wideMul a[3] b[3])) (wideMul a[4] b[2])) (shiftWide d5)
  | .xRight =>
    wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul b[2] a[4]))) (shiftWide d5)
  | .yLeft | .yRight =>
    wideAdd (wideAddRev (wideMul b[4] a[2]) (wideAdd (wideMul b[3] a[3]) (wideMul a[4] b[2]))) (shiftWide d5)

def r1 (s : Schedule) (a b : Limbs) (r0 d6 : Wide) : Wide :=
  match s with
  | .diagonal =>
    wideAdd (wideAdd (wideAdd (wideMul a[0] b[1]) (wideMul a[1] b[0])) (wideMul (low52 d6) 0x1000003d10))
        (ofWord (high52 r0))
  | .reverseCarry =>
    wideAdd (wideAddRev (wideMul (low52 d6) 0x1000003d10) (wideAdd (wideMul a[0] b[1]) (wideMul a[1] b[0])))
        (ofWord (high52 r0))
  | .fullCarry =>
    wideAdd (wideAdd (wideAdd (wideMul a[0] b[1]) (wideMul a[1] b[0])) (wideMul (low52 d6) 0x1000003d10))
        (shiftWide r0)
  | .xRight | .yRight =>
    wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul b[0] a[1])) (wideMul (low52 d6) 0x1000003d10))
        (shiftWide r0)
  | .yLeft =>
    wideAdd (wideAdd (wideAdd (wideMul b[1] a[0]) (wideMul a[1] b[0])) (wideMul (low52 d6) 0x1000003d10))
        (ofWord (high52 r0))

def d7 (s : Schedule) (a b : Limbs) (d6 : Wide) : Wide :=
  match s with
  | .diagonal | .reverseCarry =>
    wideAdd (wideAddRev (wideMul a[3] b[4]) (wideMul a[4] b[3])) (ofWord (high52 d6))
  | .fullCarry =>
    wideAdd (wideAdd (wideMul a[3] b[4]) (wideMul a[4] b[3])) (shiftWide d6)
  | .xRight | .yRight =>
    wideAdd (wideAdd (wideMul b[4] a[3]) (wideMul b[3] a[4])) (shiftWide d6)
  | .yLeft =>
    wideAdd (wideAdd (wideMul b[4] a[3]) (wideMul a[4] b[3])) (shiftWide d6)

def r2 (s : Schedule) (a b : Limbs) (r1 d7 : Wide) : Wide :=
  match s with
  | .diagonal =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0] b[2]) (wideMul a[1] b[1])) (wideMul a[2] b[0])) (wideMul
        (low52 d7) 0x1000003d10)) (ofWord (high52 r1))
  | .reverseCarry =>
    wideAdd (wideAddRev (wideMul (low52 d7) 0x1000003d10) (wideAdd (wideAdd (wideMul a[0] b[2]) (wideMul a[1]
        b[1])) (wideMul a[2] b[0]))) (ofWord (high52 r1))
  | .fullCarry =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul a[0] b[2]) (wideMul a[1] b[1])) (wideMul a[2] b[0])) (wideMul
        (low52 d7) 0x1000003d10)) (shiftWide r1)
  | .xRight =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul b[0] a[2])) (wideMul b[2] a[0])) (wideMul
        (low52 d7) 0x1000003d10)) (shiftWide r1)
  | .yLeft | .yRight =>
    wideAdd (wideAdd (wideAdd (wideAdd (wideMul b[1] a[1]) (wideMul a[2] b[0])) (wideMul b[2] a[0])) (wideMul
        (low52 d7) 0x1000003d10)) (shiftWide r1)

def r3 (s : Schedule) (d3 d7 r2 : Wide) : Wide :=
  match s with
  | .diagonal =>
    wideAdd (wideAddRev (ofWord (low52 d3)) (wideMul (high52 d7) 0x1000003d10)) (ofWord (high52 r2))
  | .reverseCarry =>
    wideAdd (wideAdd (wideMul (high52 d7) 0x1000003d10) (ofWord (low52 d3))) (ofWord (high52 r2))
  | .fullCarry | .xRight | .yLeft | .yRight =>
    wideAdd (wideAddRev (ofWord (low52 d3)) (scaleWide d7)) (shiftWide r2)

def words (s : Schedule) (a b : Limbs) : Limbs :=
  let c8 := c8 s a b
  let d3 := d3 s a b c8
  let d4 := d4 s a b c8 d3
  let d5 := d5 s a b d4
  let r0 := r0 s a b d4 d5
  let d6 := d6 s a b d5
  let r1 := r1 s a b r0 d6
  let d7 := d7 s a b d6
  let r2 := r2 s a b r1 d7
  let r3 := r3 s d3 d7 r2
  #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]

private theorem c8_eq (s : Schedule) (a b : Limbs) :
    c8 s a b = c8 .diagonal a b := by
  cases s <;> simp only [c8, wideMul_comm] <;> rfl

private theorem d3_eq (s : Schedule) (a b : Limbs) (c8 : Wide) :
    d3 s a b c8 = d3 .diagonal a b c8 := by
  cases s <;> simp only [d3, wideAddRev_eq, wideAdd_assoc, wideAdd_comm, wideMul_comm] <;> rfl

private theorem d4_eq (s : Schedule) (a b : Limbs) (c8 d3 : Wide) (hc8 : c8.2 >>> 52 = 0) (hd3 : d3.2 >>> 52 = 0) :
    d4 s a b c8 d3 = d4 .diagonal a b c8 d3 := by
  cases s <;> simp only [d4, shiftWide, scaleWide, scaleHigh_eq, shrd52_eq, hc8, hd3, wideAddRev_eq,
      wideAdd_assoc, wideAdd_comm, wideMul_comm] <;> rfl

private theorem d5_eq (s : Schedule) (a b : Limbs) (d4 : Wide) (hd4 : d4.2 >>> 52 = 0) :
    d5 s a b d4 = d5 .diagonal a b d4 := by
  cases s <;> simp only [d5, shiftWide, hd4, wideAddRev_eq, wideAdd_assoc, wideAdd_comm, wideMul_comm] <;> rfl

private theorem r0_eq (s : Schedule) (a b : Limbs) (d4 d5 : Wide) :
    r0 s a b d4 d5 = r0 .diagonal a b d4 d5 := by
  cases s <;> simp only [r0, wideAddRev_eq, wideMul_comm] <;> rfl

private theorem d6_eq (s : Schedule) (a b : Limbs) (d5 : Wide) (hd5 : d5.2 >>> 52 = 0) :
    d6 s a b d5 = d6 .diagonal a b d5 := by
  cases s <;> simp only [d6, shiftWide, hd5, wideAddRev_eq, wideAdd_assoc, wideAdd_comm, wideMul_comm] <;> rfl

private theorem r1_eq (s : Schedule) (a b : Limbs) (r0 d6 : Wide) (hr0 : r0.2 >>> 52 = 0) :
    r1 s a b r0 d6 = r1 .diagonal a b r0 d6 := by
  cases s <;> simp only [r1, shiftWide, hr0, wideAddRev_eq, wideAdd_comm, wideMul_comm] <;> rfl

private theorem d7_eq (s : Schedule) (a b : Limbs) (d6 : Wide) (hd6 : d6.2 >>> 52 = 0) :
    d7 s a b d6 = d7 .diagonal a b d6 := by
  cases s <;> simp only [d7, shiftWide, hd6, wideAddRev_eq, wideAdd_comm, wideMul_comm] <;> rfl

private theorem r2_eq (s : Schedule) (a b : Limbs) (r1 d7 : Wide) (hr1 : r1.2 >>> 52 = 0) :
    r2 s a b r1 d7 = r2 .diagonal a b r1 d7 := by
  cases s <;> simp only [r2, shiftWide, hr1, wideAddRev_eq, wideAdd_assoc, wideAdd_comm, wideMul_comm] <;> rfl

private theorem r3_eq (s : Schedule) (d3 d7 r2 : Wide) (hd7 : d7.2 >>> 52 = 0) (hr2 : r2.2 >>> 52 = 0) :
    r3 s d3 d7 r2 = r3 .diagonal d3 d7 r2 := by
  cases s <;> simp only [r3, shiftWide, scaleWide, scaleHigh_eq, shrd52_eq, hd7, hr2, wideAddRev_eq,
      wideAdd_comm, wideMul_comm] <;> rfl

private theorem limbBound {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) (i : Fin 5) :
    BoundedValue a[i].toNat a[i].toNat (if i.val < 4 then 16 * (2^52-1) else 16 * (2^48-1)) := by
  refine ⟨rfl, ?_⟩
  have hi := h.1 i
  split <;> rename_i he <;> simpa only [he, ite_true, ite_false, getElem!_pos, i.isLt] using hi

private theorem carry_zero {w : Wide} {value upper : Nat}
    (h : BoundedValue (wideValue w) value upper) (bound : upper < 2^116 := by decide) :
    w.2 >>> 52 = 0 := by
  have hw : wideValue w ≤ upper := h.eq ▸ h.le
  change w.1.toNat + 2^64 * w.2.toNat ≤ upper at hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w.2.toNat / 2^52 = 0
  omega

theorem words_eq (s : Schedule) (a b : Limbs) {x y : Fin modulus}
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    words s a b = Field.mulWords a b := by
  let hp (i j : Fin 5) := (limbBound ha i).wideMul (limbBound hb j)
  have hR : BoundedValue (0x1000003d10 : Word).toNat 0x1000003d10 0x1000003d10 := ⟨rfl, Nat.le_refl _⟩
  have hr : BoundedValue (0x1000003d1 : Word).toNat 0x1000003d1 0x1000003d1 := ⟨rfl, Nat.le_refl _⟩
  have c₈ := hp 4 4
  have c₃ := (((hp 0 3).wideAdd (hp 1 2)).wideAdd (hp 2 1)).wideAdd (hp 3 0)
  have d₃ := c₃.wideAdd (c₈.low52.wideMul hR)
  have c₄ := ((((hp 0 4).wideAdd (hp 1 3)).wideAdd (hp 2 2)).wideAdd (hp 3 1)).wideAdd (hp 4 0)
  have d₄ := (c₄.wideAdd (c₈.high52.wideMul hR)).wideAdd d₃.high52.ofWord
  have c₅ := (((hp 1 4).wideAddRev (hp 2 3)).wideAdd (hp 3 2)).wideAdd (hp 4 1)
  have d₅ := c₅.wideAdd d₄.high52.ofWord
  have r₀ := ((d₅.combine56 d₄).wideMul hr).wideAdd (hp 0 0)
  have c₆ := ((hp 2 4).wideAddRev (hp 3 3)).wideAdd (hp 4 2)
  have d₆ := c₆.wideAdd d₅.high52.ofWord
  have c₁ := (hp 0 1).wideAdd (hp 1 0)
  have r₁ := (c₁.wideAdd (d₆.low52.wideMul hR)).wideAdd r₀.high52.ofWord
  have c₇ := (hp 3 4).wideAddRev (hp 4 3)
  have d₇ := c₇.wideAdd d₆.high52.ofWord
  have c₂ := ((hp 0 2).wideAdd (hp 1 1)).wideAdd (hp 2 0)
  have r₂ := (c₂.wideAdd (d₇.low52.wideMul hR)).wideAdd r₁.high52.ofWord

  let wc8 := c8 .diagonal a b
  have zc8 : (wc8).2 >>> 52 = 0 := carry_zero c₈
  let wd3 := d3 .diagonal a b wc8
  have zd3 : (wd3).2 >>> 52 = 0 := carry_zero d₃
  let wd4 := d4 .diagonal a b wc8 wd3
  have zd4 : (wd4).2 >>> 52 = 0 := carry_zero d₄
  let wd5 := d5 .diagonal a b wd4
  have zd5 : (wd5).2 >>> 52 = 0 := carry_zero d₅
  let wr0 := r0 .diagonal a b wd4 wd5
  have zr0 : (wr0).2 >>> 52 = 0 := carry_zero r₀
  let wd6 := d6 .diagonal a b wd5
  have zd6 : (wd6).2 >>> 52 = 0 := carry_zero d₆
  let wr1 := r1 .diagonal a b wr0 wd6
  have zr1 : (wr1).2 >>> 52 = 0 := carry_zero r₁
  let wd7 := d7 .diagonal a b wd6
  have zd7 : (wd7).2 >>> 52 = 0 := carry_zero d₇
  let wr2 := r2 .diagonal a b wr1 wd7
  have zr2 : (wr2).2 >>> 52 = 0 := carry_zero r₂
  let actc8 := c8 s a b
  have ec8 : actc8 = wc8 := (c8_eq s a b )
  let actd3 := d3 s a b actc8
  have ed3 : actd3 = wd3 := (congr (rfl : d3 s a b = d3 s a b) ec8).trans (d3_eq s a b wc8 )
  let actd4 := d4 s a b actc8 actd3
  have ed4 : actd4 = wd4 := (congr (congr (rfl : d4 s a b = d4 s a b) ec8) ed3).trans (d4_eq s a b wc8 wd3 zc8 zd3)
  let actd5 := d5 s a b actd4
  have ed5 : actd5 = wd5 := (congr (rfl : d5 s a b = d5 s a b) ed4).trans (d5_eq s a b wd4 zd4)
  let actr0 := r0 s a b actd4 actd5
  have er0 : actr0 = wr0 := (congr (congr (rfl : r0 s a b = r0 s a b) ed4) ed5).trans (r0_eq s a b wd4 wd5 )
  let actd6 := d6 s a b actd5
  have ed6 : actd6 = wd6 := (congr (rfl : d6 s a b = d6 s a b) ed5).trans (d6_eq s a b wd5 zd5)
  let actr1 := r1 s a b actr0 actd6
  have er1 : actr1 = wr1 := (congr (congr (rfl : r1 s a b = r1 s a b) er0) ed6).trans (r1_eq s a b wr0 wd6 zr0)
  let actd7 := d7 s a b actd6
  have ed7 : actd7 = wd7 := (congr (rfl : d7 s a b = d7 s a b) ed6).trans (d7_eq s a b wd6 zd6)
  let actr2 := r2 s a b actr1 actd7
  have er2 : actr2 = wr2 := (congr (congr (rfl : r2 s a b = r2 s a b) er1) ed7).trans (r2_eq s a b wr1 wd7 zr1)
  let wr3 := r3 .diagonal wd3 wd7 wr2
  let actr3 := r3 s actd3 actd7 actr2
  have er3 : actr3 = wr3 := (congr (congr (congr (rfl : r3 s  = r3 s ) ed3) ed7) er2).trans (r3_eq s wd3 wd7
      wr2 zd7 zr2)
  let pack (r0 r1 r2 r3 d4 : Wide) :=
    #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  change pack actr0 actr1 actr2 actr3 actd4 = pack wr0 wr1 wr2 wr3 wd4
  exact congr (congr (congr (congr (congr (rfl : pack = pack) er0) er1) er2) er3) ed4

end K256.Proofs.Common.Point.AddWords.Product
