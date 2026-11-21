import K256.Proofs.Common.Field.Multiply.Reduction
import K256.Proofs.Common.Field.SquareValue

namespace K256.Proofs.Common.Field.Multiply

open SquareValue (P)

private def radixValue (v : Vector Nat 5) : Nat :=
  v[0] + v[1] * 2^52 + v[2] * 2^104 + v[3] * 2^156 + v[4] * 2^208

private theorem radixValue_mk (a b c d e : Nat) :
    radixValue #v[a, b, c, d, e] =
      a + b * 2^52 + c * 2^104 + d * 2^156 + e * 2^208 := by
  simp [radixValue]

private theorem reduce_mod (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : Nat) :
    radixValue (reduce c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) % P =
      (c₀ + c₁ * 2^52 + c₂ * 2^104 + c₃ * 2^156 + c₄ * 2^208 +
        c₅ * 2^260 + c₆ * 2^312 + c₇ * 2^364 + c₈ * 2^416) % P := by
  unfold reduce
  extract_lets d₃ d₄ d₅ t r₀ d₆ r₁ d₇ r₂ r₃
  rw [radixValue_mk]
  let residue := r₀ % 2^52 + r₁ % 2^52 * 2^52 + r₂ % 2^52 * 2^104 +
    r₃ % 2^52 * 2^156 + (d₄ % 2^48 + r₃ / 2^52) * 2^208
  let quotient := 16 * c₈ * 2^156 + d₄ / 2^48 % 16 + 16 * (d₅ % 2^52) +
    16 * (d₆ % 2^52) * 2^52 + 16 * d₇ * 2^104
  change residue % P = _
  have h₃ : d₃ = c₃ + c₈ % 2^52 * 0x1000003d10 := rfl
  have h₄ : d₄ = c₄ + c₈ / 2^52 * 0x1000003d10 + d₃ / 2^52 := rfl
  have h₅ : d₅ = c₅ + d₄ / 2^52 := rfl
  have ht : t = d₅ % 2^52 * 16 + d₄ / 2^48 % 16 := rfl
  have h₆ : d₆ = c₆ + d₅ / 2^52 := rfl
  have h₇ : d₇ = c₇ + d₆ / 2^52 := rfl
  have g₀ : r₀ = t * 0x1000003d1 + c₀ := rfl
  have g₁ : r₁ = c₁ + d₆ % 2^52 * 0x1000003d10 + r₀ / 2^52 := rfl
  have g₂ : r₂ = c₂ + d₇ % 2^52 * 0x1000003d10 + r₁ / 2^52 := rfl
  have g₃ : r₃ = d₃ % 2^52 + d₇ / 2^52 * 0x1000003d10 + r₂ / 2^52 := rfl
  clear_value d₃ d₄ d₅ t r₀ d₆ r₁ d₇ r₂ r₃
  have hsum :
      c₀ + c₁ * 2^52 + c₂ * 2^104 + c₃ * 2^156 + c₄ * 2^208 +
        c₅ * 2^260 + c₆ * 2^312 + c₇ * 2^364 + c₈ * 2^416 = residue + P * quotient := by
    dsimp only [residue, quotient, P]
    omega
  rw [hsum, Nat.add_mul_mod_self_left]

set_option exponentiation.threshold 512 in
private theorem convolution (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Nat) :
    a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) * 2^52 +
      (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) * 2^104 +
      (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀) * 2^156 +
      (a₀ * b₄ + a₁ * b₃ + a₂ * b₂ + a₃ * b₁ + a₄ * b₀) * 2^208 +
      (a₁ * b₄ + a₂ * b₃ + a₃ * b₂ + a₄ * b₁) * 2^260 +
      (a₂ * b₄ + a₃ * b₃ + a₄ * b₂) * 2^312 +
      (a₃ * b₄ + a₄ * b₃) * 2^364 + a₄ * b₄ * 2^416 =
      (a₀ + a₁ * 2^52 + a₂ * 2^104 + a₃ * 2^156 + a₄ * 2^208) *
      (b₀ + b₁ * 2^52 + b₂ * 2^104 + b₃ * 2^156 + b₄ * 2^208) := by
  grind only

private theorem product_mod (a b : Limbs) :
    radixValue (product a b) % modulus = limbValue a * limbValue b % modulus := by
  rw [SquareValue.modulus_eq, SquareValue.limbValue_eq, SquareValue.limbValue_eq]
  simp only [getElem!_pos, Nat.reduceLT]
  dsimp only [product]
  rw [reduce_mod]
  congr 1
  exact convolution a[0].toNat a[1].toNat a[2].toNat a[3].toNat a[4].toNat
    b[0].toNat b[1].toNat b[2].toNat b[3].toNat b[4].toNat

theorem product_residue {a b out : Limbs} (h : out.map BitVec.toNat = product a b) :
    limbValue out % modulus = limbValue a * limbValue b % modulus := by
  have hout : limbValue out = radixValue (product a b) := by
    rw [← h, SquareValue.limbValue_eq]
    simp only [radixValue, Vector.getElem_map, getElem!_pos, Nat.reduceLT]
  rw [hout, product_mod]

end K256.Proofs.Common.Field.Multiply
