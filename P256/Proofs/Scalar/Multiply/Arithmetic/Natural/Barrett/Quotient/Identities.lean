import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Quotient.Accumulator

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open X86Proofs P256.Proofs.Common.Instructions.Carry

theorem addSpec_comm (a b : BitVec 64) : addSpec a b = addSpec b a := by
  simp only [addSpec, BitVec.add_comm, Int.add_comm, Nat.add_comm]

theorem adcSpec_false_fst (a b : BitVec 64) :
    (adcSpec a b (BitVec.ofBool false)).1 = (addSpec a b).1 := by
  rw [adcSpec_result]
  simp [addSpec]

theorem adcSpec_false_cf (a b : BitVec 64) :
    (adcSpec a b (BitVec.ofBool false)).2.CF = (addSpec a b).2.CF := by
  simp only [adcSpec_cf, BitVec.toNat_ofBool, Bool.toNat_false, Nat.add_zero,
    addSpec, BitVec.toNat_add, ne_eq,
    Nat.mod_eq_iff_lt (by decide : 2^64 ≠ 0), Nat.not_lt]

theorem addSpec_zero_fst (a : BitVec 64) : (addSpec a 0).1 = a := by
  simp [addSpec]

theorem addSpec_zero_cf (a : BitVec 64) : (addSpec a 0).2.CF = false := by
  simp [addSpec]

theorem adcSpec_bool_fst (a : BitVec 64) (c : Bool) :
    (adcSpec a 0 (BitVec.ofBool c)).1 =
      (adcSpec (BitVec.ofNat 64 c.toNat) a (BitVec.ofBool false)).1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [adcSpec_toNat, BitVec.toNat_ofBool, BitVec.toNat_ofNat, Bool.toNat_false,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt c.toNat_le (by decide : 1 < 2^64))]
  rw [Nat.add_comm]

theorem adcSpec_bool_cf (a : BitVec 64) (c : Bool) :
    (adcSpec a 0 (BitVec.ofBool c)).2.CF =
      (adcSpec (BitVec.ofNat 64 c.toNat) a (BitVec.ofBool false)).2.CF := by
  simp only [adcSpec_cf, BitVec.toNat_ofBool, BitVec.toNat_ofNat, Bool.toNat_false,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt c.toNat_le (by decide : 1 < 2^64))]
  rw [Nat.add_comm]

theorem bool_byte (c : Bool) : (if c then (1 : BitVec 8) else 0) = BitVec.ofNat 8 c.toNat := by
  cases c <;> rfl

theorem bool_byte_extend (c : Bool) :
    (BitVec.ofNat 8 c.toNat).setWidth 64 = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
