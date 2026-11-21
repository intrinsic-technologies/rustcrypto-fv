import K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule.Words

namespace K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule

open K256.Proofs.Common.Field X86Proofs

private abbrev B : Nat := 2^64

private theorem bit_nat (c : Bool) : (bit c).toNat = c.toNat := by cases c <;> decide

private theorem adc_value (c : Bool) (x y : Word) :
    (x + y + bit c).toNat + B * (adcSpec c x y).2.CF.toNat = x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  change (x + y + bit c).toNat + B * (decide ((x + y + bit c).toNat ≠ _)).toNat = _
  simp only [BitVec.toNat_add, bit_nat, Nat.mod_add_mod, B, Nat.reducePow]
  have hn : x.toNat + y.toNat + c.toNat < 2 * 18446744073709551616 := by omega
  generalize x.toNat + y.toNat + c.toNat = n at hn ⊢
  by_cases h : n % 18446744073709551616 = n
  · simp only [h, ne_self_iff_false, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
  · rw [decide_eq_true h]
    change _ + _ * 1 = _
    omega

private theorem add_value (x y : Word) :
    (x + y).toNat + B * (addSpec x y).2.CF.toNat = x.toNat + y.toNat := by
  rw [addSpec_CF_toNat, BitVec.toNat_add]
  exact Nat.mod_add_div _ _

private def pair (x : Wide) : Nat := pairNat x.1 x.2

private def value (x : Column) : Nat := x.lo.toNat + B * (x.mid.toNat + B * x.hi.toNat)

private def rest (x : Column) : Nat := pair (x.mid, x.hi)

private theorem addWide_value (x y : Wide) :
    pair (addWide x y).1 + (2^128) * (addWide x y).2.toNat = pair x + pair y := by
  have lo := add_value x.1 y.1
  have hi := adc_value (addSpec x.1 y.1).2.CF x.2 y.2
  simp only [pair, pairNat, addWide, B, Nat.reducePow] at *
  omega

private theorem high_bound (a b : Word) : (Multiply.wideMul a b).2.toNat + 1 < B := by
  have hm := SquareValue.pair_mul a b
  have ha : a.toNat ≤ 2^64 - 1 := Nat.le_pred_of_lt a.isLt
  have hb : b.toNat ≤ 2^64 - 1 := Nat.le_pred_of_lt b.isLt
  have h := Nat.mul_le_mul ha hb
  simp only [pairNat, Multiply.wideMul, B, Nat.reducePow] at *
  omega

private theorem first_value (carry : Word) (p q : Wide) (hq : q.2.toNat + 1 < B) :
    value (first carry p q) = carry.toNat + pair p + pair q := by
  have s := add_value carry p.1
  have t := add_value (carry + p.1) q.1
  have m := adc_value (addSpec carry p.1).2.CF (q.2 + bit (addSpec (carry + p.1) q.1).2.CF) p.2
  have limit (c : Bool) : c.toNat ≤ 1 := by cases c <;> decide
  have hc := limit (addSpec (carry + p.1) q.1).2.CF
  simp only [first, value, pair, pairNat, bit_nat, B, BitVec.toNat_add, Nat.reducePow,
    Nat.add_comm q.1.toNat] at *
  omega

private theorem bit_sum (a b c : Bool) :
    (bit a + bit b + bit c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem four_bit_sum (a b c d : Bool) :
    (bit a + (bit b + bit c) + bit d).toNat = a.toNat + (b.toNat + c.toNat) + d.toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem three_value (prev : Column) (p q r : Wide) :
    value (three prev p q r) = rest prev + pair p + pair q + pair r := by
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  let c := addWide b.1 r
  have ea : pair a.1 + 2^128 * a.2.toNat = rest prev + pair p := addWide_value _ _
  have eb : pair b.1 + 2^128 * b.2.toNat = pair a.1 + pair q := addWide_value _ _
  have ec : pair c.1 + 2^128 * c.2.toNat = pair b.1 + pair r := addWide_value _ _
  change c.1.1.toNat + B * (c.1.2.toNat + B * (bit b.2 + bit a.2 + bit c.2).toNat) = _
  rw [bit_sum]
  simp only [pair, pairNat, B, Nat.reducePow] at *
  omega

private theorem four_value (prev : Column) (p q r s : Wide) :
    value (four prev p q r s) = rest prev + pair p + pair q + pair r + pair s := by
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  let c := addWide b.1 r
  let d := addWide c.1 s
  have ea : pair a.1 + 2^128 * a.2.toNat = rest prev + pair p := addWide_value _ _
  have eb : pair b.1 + 2^128 * b.2.toNat = pair a.1 + pair q := addWide_value _ _
  have ec : pair c.1 + 2^128 * c.2.toNat = pair b.1 + pair r := addWide_value _ _
  have ed : pair d.1 + 2^128 * d.2.toNat = pair c.1 + pair s := addWide_value _ _
  change d.1.1.toNat + B * (d.1.2.toNat + B * (bit c.2 + (bit b.2 + bit a.2) + bit d.2).toNat) = _
  rw [four_bit_sum]
  simp only [pair, pairNat, B, Nat.reducePow] at *
  omega

private theorem last_value (prev : Column) (p q top : Wide) :
    value (last prev p q top) = (rest prev + pair p + pair q + B * pair top) % (2^192) := by
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  have ea : pair a.1 + 2^128 * a.2.toNat = rest prev + pair p := addWide_value _ _
  have eb : pair b.1 + 2^128 * b.2.toNat = pair a.1 + pair q := addWide_value _ _
  have ec := add_value b.1.2 top.1
  have ha : a.2.toNat ≤ 1 := by cases a.2 <;> decide
  have width := b.1.1.isLt
  have w := (b.1.2 + top.1).isLt
  change b.1.1.toNat + B * ((b.1.2 + top.1).toNat + B *
    (bit b.2 + (top.2 + bit a.2) + bit (addSpec b.1.2 top.1).2.CF).toNat) = _
  simp only [pair, pairNat, B, BitVec.toNat_add, bit_nat, Nat.reducePow] at *
  omega

private theorem convolution (a b : Vector Word 4) (p : Fin 4 → Fin 4 → Wide)
    (hp : ∀ i j, p i j = Multiply.wideMul b[j] a[i]) :
    scalarValue a * scalarValue b =
      pair (p 0 0) + B * (
      pair (p 0 1) + pair (p 1 0) + B * (
      pair (p 0 2) + pair (p 1 1) + pair (p 2 0) + B * (
      pair (p 0 3) + pair (p 1 2) + pair (p 2 1) + pair (p 3 0) + B * (
      pair (p 1 3) + pair (p 2 2) + pair (p 3 1) + B * (
      pair (p 2 3) + pair (p 3 2) + B * pair (p 3 3)))))) := by
  simp only [hp, pair, Multiply.wideMul, SquareValue.pair_mul, scalarValue,
    Nat.add_mul, Nat.mul_add]
  ac_rfl

set_option exponentiation.threshold 512 in
theorem machineProduct_eq (a b : Vector Word 4) : machineProduct a b = productWords a b := by
  let p (i j : Fin 4) := Multiply.wideMul b[j] a[i]
  let c₁ := first (p 0 0).2 (p 0 1) (p 1 0)
  let c₂ := three c₁ (p 0 2) (p 1 1) (p 2 0)
  let c₃ := four c₂ (p 0 3) (p 1 2) (p 2 1) (p 3 0)
  let c₄ := three c₃ (p 1 3) (p 2 2) (p 3 1)
  let c₅ := last c₄ (p 2 3) (p 3 2) (p 3 3)
  have h₁ : value c₁ = _ := first_value (p 0 0).2 (p 0 1) (p 1 0) (high_bound _ _)
  have h₂ : value c₂ = _ := three_value c₁ (p 0 2) (p 1 1) (p 2 0)
  have h₃ : value c₃ = _ := four_value c₂ (p 0 3) (p 1 2) (p 2 1) (p 3 0)
  have h₄ : value c₄ = _ := three_value c₃ (p 1 3) (p 2 2) (p 3 1)
  have h₅ : value c₅ = _ := last_value c₄ (p 2 3) (p 3 2) (p 3 3)
  have hc := convolution a b p (fun _ _ => rfl)
  have hn : scalarValue a * scalarValue b < 2^512 := by
    rw [show (2:Nat)^512 = 2^256 * 2^256 by decide +kernel]
    exact Nat.mul_lt_mul_of_lt_of_le (scalarValue_lt a) (Nat.le_of_lt (scalarValue_lt b)) (by decide)
  have h₀ : pair (p 0 0) = (p 0 0).1.toNat + B * (p 0 0).2.toNat := rfl
  apply wideValue_injective
  rw [productWords_value]
  change (p 0 0).1.toNat + B * (c₁.lo.toNat + B * (c₂.lo.toNat + B * (c₃.lo.toNat +
    B * (c₄.lo.toNat + B * value c₅)))) = _
  simp only [value, rest, pair, pairNat, B, Nat.reducePow] at h₁ h₂ h₃ h₄ h₅ h₀ hc ⊢
  omega

end K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule
