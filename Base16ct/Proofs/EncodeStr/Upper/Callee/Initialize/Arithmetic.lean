import Base16ct.Proofs.EncodeStr.Upper.Callee.State

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem init_input_length_lt_32 (c : CallContext) : c.input.length < 2^32 := by
  have h := c.valid.inputInMemory.2.1
  have h : (c.initial.regValue .rdi).toNat + c.input.length < 2^32 := by
    simpa only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit, List.size_toByteArray] using h
  omega

theorem init_input_length_lt_62 (c : CallContext) : c.input.length < 2^62 := by
  have h := init_input_length_lt_32 c
  omega

theorem init_input_length_lt_63 (c : CallContext) : c.input.length < 2^63 := by
  have h := init_input_length_lt_32 c
  omega

theorem init_input_length_lt_64 (c : CallContext) : c.input.length < 2^64 := by
  have h := init_input_length_lt_32 c
  omega

theorem init_double_input_length_lt_64 (c : CallContext) : 2 * c.input.length < 2^64 := by
  have h := init_input_length_lt_32 c
  omega

theorem init_capacity_lt_32 (c : CallContext) : c.capacity < 2^32 := by
  have h := c.valid.outputInMemory.2.1
  change (c.initial.regValue .rcx).toNat + c.capacity < 2^32 at h
  omega

theorem init_capacity_lt_64 (c : CallContext) : c.capacity < 2^64 := by
  have h := init_capacity_lt_32 c
  omega

theorem init_input_length_add_self (c : CallContext) :
    BitVec.ofNat 64 c.input.length + BitVec.ofNat 64 c.input.length =
      BitVec.ofNat 64 (2 * c.input.length) := by
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem init_double_input_length_le_capacity (c : CallContext) :
    BitVec.ofNat 64 (2 * c.input.length) ≤ BitVec.ofNat 64 c.capacity ↔
      2 * c.input.length ≤ c.capacity := by
  simp only [BitVec.le_def, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (init_double_input_length_lt_64 c),
    Nat.mod_eq_of_lt (init_capacity_lt_64 c)]

theorem init_double_input_length_ule_capacity (c : CallContext) :
    (BitVec.ofNat 64 (2 * c.input.length)).ule (BitVec.ofNat 64 c.capacity) = true ↔
      2 * c.input.length ≤ c.capacity := by
  rw [BitVec.ule_iff_le, init_double_input_length_le_capacity]

theorem init_input_length_mask (c : CallContext) :
    BitVec.ofNat 64 c.input.length &&& 0x3fffffffffffffff =
      BitVec.ofNat 64 c.input.length := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (init_input_length_lt_64 c)]
  change c.input.length &&& (2^62 - 1) = c.input.length
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (init_input_length_lt_62 c)

theorem init_input_length_eq_zero (c : CallContext) :
    BitVec.ofNat 64 c.input.length = 0 ↔ c.input.length = 0 := by
  rw [← BitVec.toNat_inj]
  change c.input.length % 2^64 = 0 ↔ c.input.length = 0
  rw [Nat.mod_eq_of_lt (init_input_length_lt_64 c)]

end Base16ct.Proofs.EncodeStr.Upper
