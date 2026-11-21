import P256.Spec.Operations

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Scalar

structure Limbs where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64

def Limbs.toNat (a : Limbs) : Nat :=
  a.l0.toNat + 2^64 * (a.l1.toNat + 2^64 * (a.l2.toNat + 2^64 * a.l3.toNat))

theorem shift63_toNat (a : BitVec 64) : (a >>> 63).toNat = a.msb.toNat := by
  have ha := a.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  by_cases h : 2^63 ≤ a.toNat <;>
    simp only [show 64-1=63 from rfl, h, decide_true, decide_false,
      Bool.toNat_true, Bool.toNat_false] <;> omega

theorem eq_zero_or_one {b : BitVec 64} (hb : b.toNat ≤ 1) : b = 0 ∨ b = 1 := by
  by_cases h : b.toNat = 0
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · right
    apply BitVec.eq_of_toNat_eq
    change b.toNat = 1
    omega

theorem limbs_toNat_lt (a : Limbs) : a.toNat < 2^256 := by
  have h0 := a.l0.isLt
  have h1 := a.l1.isLt
  have h2 := a.l2.isLt
  have h3 := a.l3.isLt
  simp only [Limbs.toNat]
  omega

theorem subtractWord_toNat (a b : BitVec 64) (k : Nat) (hk : k < 2^64)
    (hb : b = 0 ∨ b = 1) :
    (a + (-b).sshiftRight 63 + BitVec.ofNat 64 (2^64-k)).toNat =
      (2^64 + a.toNat - k - b.toNat) % 2^64 := by
  have ha := a.isLt
  rcases hb with rfl | rfl
  · rw [show (-(0 : BitVec 64)).sshiftRight 63 = 0 by decide +kernel]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    change ((a.toNat+0)%2^64 + (2^64-k)%2^64)%2^64 = (2^64+a.toNat-k-0)%2^64
    rw [Nat.add_zero, Nat.mod_eq_of_lt ha, Nat.add_mod_mod]
    exact congrArg (fun x : Nat => x % 2^64) (by omega)
  · rw [show (-(1 : BitVec 64)).sshiftRight 63 = -1 by decide +kernel]
    rw [BitVec.toNat_add, BitVec.toNat_add]
    rw [BitVec.toNat_ofNat]
    change ((a.toNat + 18446744073709551615)%2^64 + (2^64-k)%2^64)%2^64 =
      (2^64+a.toNat-k-1)%2^64
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]
    omega

theorem subtractWord_borrow_or (a r : BitVec 64) (k b : Nat)
    (hk : 2^63 ≤ k) (hk' : k < 2^64) (hb : b ≤ 1)
    (hr : r.toNat = (2^64+a.toNat-k-b)%2^64) :
    ((~~~a ||| r) >>> 63).toNat ≤ 1 ∧
    r.toNat + k + b = a.toNat + 2^64 * ((~~~a ||| r) >>> 63).toNat := by
  have ha := a.isLt
  have hr' := r.isLt
  rw [shift63_toNat, BitVec.msb_or, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide, show decide (0 < 64) = true from rfl, Bool.true_and]
  by_cases h₁ : 2^63 ≤ a.toNat <;>
    by_cases h₂ : 2^63 ≤ r.toNat <;>
    simp only [show 64-1=63 from rfl, h₁, h₂, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
      Bool.toNat_true, Bool.toNat_false] <;> omega

theorem limbs_ofNat_toNat (d : Nat) (hd : d < 2 ^ 256) :
    (Limbs.mk (BitVec.ofNat 64 d) (BitVec.ofNat 64 (d / 2 ^ 64))
      (BitVec.ofNat 64 (d / 2 ^ 128)) (BitVec.ofNat 64 (d / 2 ^ 192))).toNat = d := by
  simp only [Limbs.toNat, BitVec.toNat_ofNat]
  omega

end P256.Proofs.SecretKeyFromBytes.Scalar
