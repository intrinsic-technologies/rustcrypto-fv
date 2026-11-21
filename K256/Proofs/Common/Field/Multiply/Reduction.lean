import K256.Proofs.Common.Field.Repr

namespace K256.Proofs.Common.Field.Multiply

def reduce (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : Nat) : Vector Nat 5 :=
  let d₃ := c₃ + c₈ % 2^52 * 0x1000003d10
  let d₄ := c₄ + c₈ / 2^52 * 0x1000003d10 + d₃ / 2^52
  let d₅ := c₅ + d₄ / 2^52
  let t := d₅ % 2^52 * 16 + d₄ / 2^48 % 16
  let r₀ := t * 0x1000003d1 + c₀
  let d₆ := c₆ + d₅ / 2^52
  let r₁ := c₁ + d₆ % 2^52 * 0x1000003d10 + r₀ / 2^52
  let d₇ := c₇ + d₆ / 2^52
  let r₂ := c₂ + d₇ % 2^52 * 0x1000003d10 + r₁ / 2^52
  let r₃ := d₃ % 2^52 + d₇ / 2^52 * 0x1000003d10 + r₂ / 2^52
  #v[r₀ % 2^52, r₁ % 2^52, r₂ % 2^52, r₃ % 2^52, d₄ % 2^48 + r₃ / 2^52]

def product (a b : Limbs) : Vector Nat 5 :=
  let p (i j : Fin 5) := a[i].toNat * b[j].toNat
  reduce (p 0 0) (p 0 1 + p 1 0) (p 0 2 + p 1 1 + p 2 0)
    (p 0 3 + p 1 2 + p 2 1 + p 3 0) (p 0 4 + p 1 3 + p 2 2 + p 3 1 + p 4 0)
    (p 1 4 + p 2 3 + p 3 2 + p 4 1) (p 2 4 + p 3 3 + p 4 2) (p 3 4 + p 4 3) (p 4 4)

end K256.Proofs.Common.Field.Multiply
