import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open Prelude X86 X86.Machine X86Proofs
open P256.Proofs.Field

theorem montgomery_limbs_eq_iff {s t : RamState} {a b : BitVec 64} {x y : Nat}
    (hx : MontgomeryAt s a x) (hy : MontgomeryAt t b y) :
    (∀ j < 4, memLoad s.external (a + BitVec.ofNat 64 (8*j)) 64 =
      memLoad t.external (b + BitVec.ofNat 64 (8*j)) 64) ↔ x = y := by
  constructor
  · intro h
    have values : readLimbs s a = readLimbs t b := by
      have h0 := h 0 (by decide)
      have h1 := h 1 (by decide)
      have h2 := h 2 (by decide)
      have h3 := h 3 (by decide)
      simp only [Nat.mul_zero, BitVec.add_zero] at h0
      change memLoad s.external (a + 8) 64 = memLoad t.external (b + 8) 64 at h1
      change memLoad s.external (a + 16) 64 = memLoad t.external (b + 16) 64 at h2
      change memLoad s.external (a + 24) 64 = memLoad t.external (b + 24) 64 at h3
      simp only [readLimbs, h0, h1, h2, h3]
    have eq := congrArg (fun v : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs => v.toNat) values
    rw [readLimbs_toNat hx.2, readLimbs_toNat hy.2] at eq
    have canceled := congrArg (fun n => n * Montgomery.radixInverse % Montgomery.p) eq
    simpa only [Nat.mod_mul_mod, Nat.mul_assoc,
      Nat.mul_mod _ (2^256 * Montgomery.radixInverse), Montgomery.radix_mul_inverse,
      Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using canceled
  · intro h j hj
    rw [hx.memLoad_limb j hj, hy.memLoad_limb j hj, h]

theorem four_limb_xor_or_eq_zero (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    ((a3 ^^^ b3) ||| ((a2 ^^^ b2) ||| ((a0 ^^^ b0) ||| (a1 ^^^ b1)))) = 0 ↔
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  change ((a3 ^^^ b3) ||| ((a2 ^^^ b2) ||| ((a0 ^^^ b0) ||| (a1 ^^^ b1)))) = 0#64 ↔ _
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · intro h; exact ⟨h.2.2.1, h.2.2.2, h.2.1, h.1⟩
  · intro h; exact ⟨h.2.2.2, h.2.2.1, h.1, h.2.1⟩

end P256.Proofs.Sec1.SquareRoot
