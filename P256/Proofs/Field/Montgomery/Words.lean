import P256.Proofs.Field.Montgomery.Arithmetic
import P256.Proofs.Common.Instructions.Carry.Arithmetic
import P256.Proofs.Common.Instructions.Mul.Spec

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

open X86Proofs
open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry
  (adcSpec adcSpec_toNat_add_carry addSpec_toNat_add_carry)

def add64 (a b : BitVec 64) : BitVec 64 × Bool :=
  ((addSpec a b).1, (addSpec a b).2.CF)

def adc64 (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  ((adcSpec a b (BitVec.ofBool c)).1, (adcSpec a b (BitVec.ofBool c)).2.CF)

def product64 (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  (a * b, mulHigh64 a b)

theorem add64_value (a b : BitVec 64) :
    (add64 a b).1.toNat + wordBase * (add64 a b).2.toNat = a.toNat + b.toNat :=
  addSpec_toNat_add_carry a b

theorem adc64_value (a b : BitVec 64) (c : Bool) :
    (adc64 a b c).1.toNat + wordBase * (adc64 a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  simpa only [adc64, wordBase, BitVec.toNat_ofBool] using
    adcSpec_toNat_add_carry a b (BitVec.ofBool c)

theorem product64_value (a b : BitVec 64) :
    (product64 a b).1.toNat + wordBase * (product64 a b).2.toNat = a.toNat * b.toNat := by
  have hb : a.toNat * b.toNat < 2^64 * 2^64 :=
    Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  have hh : (mulHigh64 a b).toNat = a.toNat * b.toNat / 2^64 := by
    change (a.toNat * b.toNat / 2^64) % 2^64 = _
    apply Nat.mod_eq_of_lt
    omega
  change (a*b).toNat + wordBase * (mulHigh64 a b).toNat = _
  rw [hh, BitVec.toNat_mul]
  exact Nat.mod_add_div _ _

end P256.Proofs.Field.Montgomery
