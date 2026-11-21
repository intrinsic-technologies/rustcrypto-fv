import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Wrapper

open X86 X86.Machine X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem byte_mod_radix (x i : Nat) (hi : i < 32) :
    (x % 2^256) / 256^i % 256 = x / 256^i % 256 := by
  have hradix : 256^i * (256 * 256^(31-i)) = 2^256 := by
    calc
      _ = 256^(i+(1+(31-i))) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
      _ = 256^32 := by congr 1; omega
      _ = 2^256 := by decide +kernel
  rw [← hradix, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem low_nat256 {s : RamState} {address : BitVec 64} {x : Nat}
    (h : Bytes s.external address 64 (fun i => UInt8.ofNat (x / 256^i % 256))) :
    Nat256At s address (x % 2^256) := by
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  intro i hi
  rw [byte_mod_radix x i hi]
  exact h i (by omega)

theorem high_nat256 {s : RamState} {address : BitVec 64} {x : Nat}
    (h : Bytes s.external address 64 (fun i => UInt8.ofNat (x / 256^i % 256)))
    (hx : x < 2^256 * 2^256) : Nat256At s (address + 32) (x / 2^256) := by
  refine ⟨(Nat.div_lt_iff_lt_mul (by decide : 0 < 2^256)).mpr hx, ?_⟩
  intro i hi
  have he : 256^(32+i) = 2^256 * 256^i := by
    rw [Nat.pow_add]
  have hb := h (32+i) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, he, Nat.div_div_eq_div_mul] using hb

end P256.Proofs.Field.Montgomery.Wrapper
