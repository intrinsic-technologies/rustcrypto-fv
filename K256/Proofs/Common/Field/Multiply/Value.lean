import K256.Proofs.Common.Field.Multiply.Bounds
import K256.Proofs.Common.Field.Multiply.Reduction

namespace K256.Proofs.Common.Field.Multiply

private theorem limbBound {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) (i : Fin 5) :
    BoundedValue a[i].toNat a[i].toNat (if i.val < 4 then 16 * (2^52-1) else 16 * (2^48-1)) := by
  refine ⟨rfl, ?_⟩
  have hi := h.1 i
  split <;> rename_i he <;> simpa only [he, ite_true, ite_false, getElem!_pos, i.isLt] using hi

private theorem mapFive {a b c d e : Word} {v w x y z : Nat}
    (ha : a.toNat = v) (hb : b.toNat = w) (hc : c.toNat = x) (hd : d.toNat = y) (he : e.toNat = z) :
    (#v[a,b,c,d,e].map BitVec.toNat) = #v[v,w,x,y,z] := by
  subst ha hb hc hd he
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem fiveBounds {a b c d e : Word}
    (ha : a.toNat ≤ 2^52-1) (hb : b.toNat ≤ 2^52-1) (hc : c.toNat ≤ 2^52-1)
    (hd : d.toNat ≤ 2^52-1) (he : e.toNat ≤ 2 * (2^48-1)) (i : Fin 5) :
    if i.val < 4 then (#v[a,b,c,d,e][i]!).toNat ≤ 2 * 1 * (2^52-1)
    else (#v[a,b,c,d,e][i]!).toNat ≤ 2 * 1 * (2^48-1) := by
  obtain ⟨i, hi⟩ := i
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · exact Nat.le_trans ha (by decide)
  · exact Nat.le_trans hb (by decide)
  · exact Nat.le_trans hc (by decide)
  · exact Nat.le_trans hd (by decide)
  · exact he

theorem mulWords_value_and_bounds {a b : Limbs} {x y : Fin modulus} (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    (mulWords a b).map BitVec.toNat = product a b ∧
    ∀ i : Fin 5, if i.val < 4 then ((mulWords a b)[i]!).toNat ≤ 2 * 1 * (2^52-1)
      else ((mulWords a b)[i]!).toNat ≤ 2 * 1 * (2^48-1) := by
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
  have r₃ := (d₃.low52.ofWord.wideAddRev (d₇.high52.wideMul hR)).wideAdd r₂.high52.ofWord
  have r₄ := d₄.low48.wordAdd r₃.high52
  refine ⟨mapFive r₀.low52.eq r₁.low52.eq r₂.low52.eq r₃.low52.eq r₄.eq, ?_⟩
  exact fiveBounds (r₀.low52.eq ▸ r₀.low52.le) (r₁.low52.eq ▸ r₁.low52.le)
    (r₂.low52.eq ▸ r₂.low52.le) (r₃.low52.eq ▸ r₃.low52.le)
    (r₄.eq ▸ Nat.le_trans r₄.le (by decide))

end K256.Proofs.Common.Field.Multiply
