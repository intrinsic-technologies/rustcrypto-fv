import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Split

open Standards.SECG.DomainParameters.Secp256k1

private abbrev base : Nat := 2^64

def scalarValue (w : Vector (BitVec 64) 4) : Nat :=
  w[0].toNat + base * (w[1].toNat + base * (w[2].toNat + base * (w[3].toNat)))

def wideValue (w : Vector (BitVec 64) 8) : Nat :=
  w[0].toNat + base * (w[1].toNat + base * (w[2].toNat + base * (w[3].toNat + base * (w[4].toNat + base * (w[5].toNat + base * (w[6].toNat + base * (w[7].toNat)))))))

theorem wideValue_injective {a b : Vector (BitVec 64) 8} (h : wideValue a = wideValue b) : a = b := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_toNat_eq
  simp only [wideValue, base, Nat.reducePow] at h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private def columns (a b : Vector (BitVec 64) 4) : Vector Nat 7 :=
  #v[a[0].toNat * b[0].toNat,
     a[0].toNat * b[1].toNat + a[1].toNat * b[0].toNat,
     a[0].toNat * b[2].toNat + a[1].toNat * b[1].toNat + a[2].toNat * b[0].toNat,
     a[0].toNat * b[3].toNat + a[1].toNat * b[2].toNat + a[2].toNat * b[1].toNat + a[3].toNat * b[0].toNat,
     a[1].toNat * b[3].toNat + a[2].toNat * b[2].toNat + a[3].toNat * b[1].toNat,
     a[2].toNat * b[3].toNat + a[3].toNat * b[2].toNat,
     a[3].toNat * b[3].toNat]

private def propagate (t : Vector Nat 7) : Vector Nat 8 :=
  let c0 := t[0]
  let c1 := t[1] + c0 / base
  let c2 := t[2] + c1 / base
  let c3 := t[3] + c2 / base
  let c4 := t[4] + c3 / base
  let c5 := t[5] + c4 / base
  let c6 := t[6] + c5 / base
  #v[c0, c1, c2, c3, c4, c5, c6, c6 / base]

def productWords (a b : Vector (BitVec 64) 4) : Vector (BitVec 64) 8 :=
  (propagate (columns a b)).map (BitVec.ofNat 64)

private def columnValue (t : Vector Nat 7) : Nat :=
  t[0] + base * (t[1] + base * (t[2] + base * (t[3] + base * (t[4] + base * (t[5] + base * (t[6]))))))

private theorem columns_value (a b : Vector (BitVec 64) 4) :
    columnValue (columns a b) = scalarValue a * scalarValue b := by
  simp only [columnValue, columns, scalarValue, List.getElem_toArray, Vector.getElem_mk,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_add, Nat.add_mul]
  ac_rfl

theorem scalarValue_lt (w : Vector (BitVec 64) 4) : scalarValue w < 2^256 := by
  have h₀ := w[0].isLt
  have h₁ := w[1].isLt
  have h₂ := w[2].isLt
  have h₃ := w[3].isLt
  simp only [scalarValue, base, Nat.reducePow]
  omega

set_option exponentiation.threshold 512 in
private theorem carry_value (t : Vector Nat 7) (bound : columnValue t < 2^512) :
    wideValue ((propagate t).map (BitVec.ofNat 64)) = columnValue t := by
  simp only [wideValue, propagate, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
  simp only [columnValue, base, Nat.reducePow] at bound ⊢
  omega

theorem productWords_value (a b : Vector (BitVec 64) 4) :
    wideValue (productWords a b) = scalarValue a * scalarValue b := by
  rw [productWords, carry_value, columns_value]
  rw [columns_value]
  rw [show (2:Nat)^512 = (2^256)*(2^256) by decide +kernel]
  exact Nat.mul_lt_mul_of_lt_of_le (scalarValue_lt a) (Nat.le_of_lt (scalarValue_lt b))
    (by decide : 0 < 2^256)

theorem scalarWords_value (x : Nat) (bound : x < 2^256) :
    scalarValue (scalarWords x) = x := by
  simp only [scalarValue, scalarWords, Vector.getElem_ofFn, BitVec.toNat_ofNat, base,
    Nat.reduceMul, Nat.reducePow, Nat.div_one]
  omega

def roundedHigh (w : Vector (BitVec 64) 8) : Nat :=
  w[6].toNat + base * w[7].toNat + (w[5] >>> 63).toNat

set_option exponentiation.threshold 512 in
theorem roundedHigh_value (w : Vector (BitVec 64) 8) :
    roundedHigh w = (wideValue w + 2^383) / 2^384 := by
  have h₀ := w[0].isLt
  have h₁ := w[1].isLt
  have h₂ := w[2].isLt
  have h₃ := w[3].isLt
  have h₄ := w[4].isLt
  have h₅ := w[5].isLt
  simp only [roundedHigh, wideValue, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, base, Nat.reducePow]
  omega

theorem rounded_product {x y : Nat} (hx : x < 2^256) (hy : y < 2^256) :
    roundedHigh (productWords (scalarWords x) (scalarWords y)) = Generate.Curve.mulShift384 x y := by
  rw [roundedHigh_value, productWords_value, scalarWords_value x hx, scalarWords_value y hy]
  rfl

theorem reduced_product {x y : Nat} (hx : x < 2^256) (hy : y < 2^256) :
    wideValue (productWords (scalarWords x) (scalarWords y)) % domain.n = (x * y) % domain.n := by
  rw [productWords_value, scalarWords_value x hx, scalarWords_value y hy]

end K256.Proofs.Generate.Generator.Multiply.Split
