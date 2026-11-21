import Standards.RFC.ChaCha20Poly1305.Poly1305

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305

abbrev B : Nat := 2^26
abbrev modulus : Nat := 2^130 - 5

structure Limbs where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat

def Limbs.value (x : Limbs) : Nat := x.x0 + B*(x.x1 + B*(x.x2 + B*(x.x3 + B*x.x4)))

def Limbs.plus (a b : Limbs) : Limbs :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4⟩

theorem plus_value (a b : Limbs) : (a.plus b).value = a.value + b.value := by
  simp only [Limbs.value, Limbs.plus, B, Nat.reducePow]
  omega

def convolution (a r : Limbs) : Limbs :=
  ⟨a.x0*r.x0 + 5*(a.x1*r.x4 + a.x2*r.x3 + a.x3*r.x2 + a.x4*r.x1),
   a.x0*r.x1 + a.x1*r.x0 + 5*(a.x2*r.x4 + a.x3*r.x3 + a.x4*r.x2),
   a.x0*r.x2 + a.x1*r.x1 + a.x2*r.x0 + 5*(a.x3*r.x4 + a.x4*r.x3),
   a.x0*r.x3 + a.x1*r.x2 + a.x2*r.x1 + a.x3*r.x0 + 5*(a.x4*r.x4),
   a.x0*r.x4 + a.x1*r.x3 + a.x2*r.x2 + a.x3*r.x1 + a.x4*r.x0⟩

def highProduct (a r : Limbs) : Nat :=
  a.x1*r.x4 + a.x2*r.x3 + a.x3*r.x2 + a.x4*r.x1 +
    B*(a.x2*r.x4 + a.x3*r.x3 + a.x4*r.x2 +
    B*(a.x3*r.x4 + a.x4*r.x3 + B*(a.x4*r.x4)))

theorem convolution_value (a r : Limbs) :
    a.value*r.value = (convolution a r).value + (highProduct a r)*modulus := by
  simp only [Limbs.value, convolution, highProduct]
  grind only [show B = 67108864 by decide, show modulus = 1361129467683753853853498429727072845819 by decide]

structure Carried where
  limbs : Limbs
  quotient : Nat

def carry (p : Limbs) : Carried :=
  let d0 := p.x0
  let d1 := p.x1 + d0/B
  let d2 := p.x2 + d1/B
  let d3 := p.x3 + d2/B
  let d4 := p.x4 + d3/B
  let t := d0%B + 5*(d4/B)
  ⟨⟨t%B, d1%B + t/B, d2%B, d3%B, d4%B⟩, d4/B⟩

theorem carry_value (p : Limbs) :
    p.value = (carry p).limbs.value + (carry p).quotient * modulus := by
  simp only [carry, Limbs.value, B, modulus, Nat.reducePow, Nat.reduceSub]
  omega

def update (a r block : Limbs) : Limbs := (carry (convolution (a.plus block) r)).limbs

theorem update_value (a r block : Limbs) :
    (update a r block).value % modulus = (r.value * (a.value + block.value)) % modulus := by
  rw [← plus_value, Nat.mul_comm, convolution_value, Nat.add_mul_mod_self_right,
    carry_value (convolution _ _), Nat.add_mul_mod_self_right]
  rfl

def splitLimbs (w : Nat) : Limbs := ⟨w%B, w/B%B, w/B^2%B, w/B^3%B, w/B^4%B⟩

theorem split_value (w : Nat) (h : w < 2^130) : (splitLimbs w).value = w := by
  simp only [splitLimbs, Limbs.value, B, Nat.reducePow]
  omega

def fullBlock (w : Nat) : Limbs := splitLimbs (w + 2^128)

theorem fullBlock_value (w : Nat) (h : w < 2^128) : (fullBlock w).value = w + 2^128 :=
  split_value _ (by omega)

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
