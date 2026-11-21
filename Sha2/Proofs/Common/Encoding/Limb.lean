import X86Proofs.Program.ReadWrite.Bytes
import Init.Data.Nat.Mod

set_option autoImplicit false

namespace Sha2.Proofs.Common.Encoding

open X86Proofs

def canonicalLimb (value index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (value / 2^(64*index))

theorem canonicalLimb_byte (value index byte : Nat) (hbyte : byte < 8) :
    storedByte (canonicalLimb value index) byte =
      UInt8.ofNat (value / 256 ^ (8 * index + byte) % 256) := by
  have hpow (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
  apply UInt8.toNat.inj
  simp only [storedByte, canonicalLimb, UInt8.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  have hsplit : 2^64 = 2^(8*byte) * 2^(64-8*byte) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (show 256 ∣ 2^(64-8*byte) from
    Nat.pow_dvd_pow 2 (show 8 ≤ 64-8*byte by omega))]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hpow]
  congr 3
  omega

end Sha2.Proofs.Common.Encoding
