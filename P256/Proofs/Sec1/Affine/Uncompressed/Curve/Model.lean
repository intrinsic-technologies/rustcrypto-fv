import P256.Proofs.Sec1.Affine.Uncompressed.Model
import P256.Proofs.Field.Constants
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec P256.Proofs.Field
open X86 X86.Machine X86Proofs

theorem coefficient_a {s : RamState} {address : BitVec 64}
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (word0 : memLoad s.external address 64 = 0xfffffffffffffffc)
    (word1 : memLoad s.external (address + 8) 64 = 0x00000003ffffffff)
    (word2 : memLoad s.external (address + 16) 64 = 0)
    (word3 : memLoad s.external (address + 24) 64 = 0xfffffffc00000004) :
    MontgomeryAt s address Operations.domain.a := by
  apply montgomeryAt_of_memLoad_limbs (by decide +kernel) allocated
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  · change memLoad s.external (address + (0 : BitVec 64)) 64 = 0xfffffffffffffffc
    exact (congrArg (fun a => memLoad s.external a 64) (BitVec.add_zero address)).trans word0
  · exact word1
  · exact word2
  · exact word3

theorem montgomery_injective {x y : Nat}
    (hx : x < Operations.domain.p) (hy : y < Operations.domain.p) :
    x * 2^256 % Operations.domain.p = y * 2^256 % Operations.domain.p ↔ x = y := by
  constructor
  · intro h
    have decoded := congrArg (fun n => n * Montgomery.radixInverse % Operations.domain.p) h
    simpa only [Nat.mod_mul_mod, Nat.mul_assoc,
      Nat.mul_mod _ (2^256 * Montgomery.radixInverse), Montgomery.radix_mul_inverse,
      Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using decoded
  · rintro rfl
    rfl

theorem prefixEqual_montgomery {s : RamState} {x y : Nat}
    (hx : MontgomeryAt s (s.regValue .rdi) x)
    (hy : MontgomeryAt s (s.regValue .rdx) y) :
    P256.Proofs.SecretKeyFromBytes.Scalar.Equal.prefixEqual s 4 = decide (x = y) := by
  simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Equal.prefixEqual_nat256 hx.2 hy.2,
    montgomery_injective hx.1 hy.1]

theorem arithmetic_eq (x : Nat) :
    (((x * x % Operations.domain.p * x % Operations.domain.p) +
      (Operations.domain.a * x % Operations.domain.p)) % Operations.domain.p +
      Operations.domain.b) % Operations.domain.p =
      (x * x * x + Operations.domain.a * x + Operations.domain.b) % Operations.domain.p := by
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]

theorem valid_arithmetic (bytes : ByteArray) :
    valid bytes = (decide (xCoordinate bytes < Operations.domain.p) &&
      decide (yCoordinate bytes < Operations.domain.p) &&
      (canonical (yCoordinate bytes) * canonical (yCoordinate bytes) % Operations.domain.p ==
        (((canonical (xCoordinate bytes) * canonical (xCoordinate bytes) % Operations.domain.p *
            canonical (xCoordinate bytes) % Operations.domain.p) +
          (Operations.domain.a * canonical (xCoordinate bytes) % Operations.domain.p)) %
            Operations.domain.p + Operations.domain.b) % Operations.domain.p)) := by
  rw [arithmetic_eq, valid_eq]

theorem valid_mask (bytes : ByteArray) :
    (((if canonical (yCoordinate bytes) * canonical (yCoordinate bytes) % Operations.domain.p ==
        (canonical (xCoordinate bytes) * canonical (xCoordinate bytes) *
          canonical (xCoordinate bytes) + Operations.domain.a * canonical (xCoordinate bytes) +
          Operations.domain.b) % Operations.domain.p then 1 else 0) : BitVec 8) &&&
      (if xCoordinate bytes < Operations.domain.p then 1 else 0)) &&&
      (if yCoordinate bytes < Operations.domain.p then 1 else 0) =
      if valid bytes then 1 else 0 := by
  rw [valid_eq]
  generalize (canonical (yCoordinate bytes) * canonical (yCoordinate bytes) % Operations.domain.p ==
    (canonical (xCoordinate bytes) * canonical (xCoordinate bytes) *
      canonical (xCoordinate bytes) + Operations.domain.a * canonical (xCoordinate bytes) +
      Operations.domain.b) % Operations.domain.p) = same
  by_cases hx : xCoordinate bytes < Operations.domain.p
  all_goals by_cases hy : yCoordinate bytes < Operations.domain.p
  all_goals cases same <;> simp [hx, hy]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
