import P256.Proofs.Program.Interface
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Program.ReadWrite.Bytes
import Init.Data.Nat.Mod

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64 bswap64_byte)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Serialize

open Prelude X86 X86.Machine X86Proofs

def canonicalLimb (value index : Nat) : BitVec 64 := BitVec.ofNat 64 (value / 2^(64*index))

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

theorem canonicalLimb_bigEndian_byte (value i : Nat) (hi : i < 32) :
    storedByte (bswap64 (canonicalLimb value (3 - i / 8))) (i % 8) =
      UInt8.ofNat (value / 256 ^ (31 - i) % 256) := by
  rw [storedByte_eq_extract, bswap64_byte _ _ (Nat.mod_lt _ (by decide))]
  rw [← storedByte_eq_extract]
  rw [canonicalLimb_byte value _ _ (by omega)]
  have he : 8 * (3 - i / 8) + (7 - i % 8) = 31 - i := by omega
  rw [he]

theorem canonical_bigEndian_bytes {t : RamState} {a : BitVec 64} {value : Nat}
    (allocated : ∀ i < 32, (t.external[a + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 4, (Operand.mem (a + BitVec.ofNat 64 (8*j)) : Operand 64).read t =
      bswap64 (canonicalLimb value (3-j))) :
    Bytes t.external a 32 (fun i => UInt8.ofNat (value / 256^(31-i) % 256)) := by
  intro i hi
  have hbytes : Bytes t.external (a + BitVec.ofNat 64 (8*(i/8))) 8
      (storedByte (bswap64 (canonicalLimb value (3-i/8)))) := by
    have h := Bytes.of_memLoad (n := 64) (a := a + BitVec.ofNat 64 (8*(i/8)))
      (m := t.external) (by
        intro j hj
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact allocated _ (by omega))
    change Bytes _ _ 8 (storedByte ((Operand.mem _ : Operand 64).read t)) at h
    rw [words (i/8) (by omega)] at h
    exact h
  have h := hbytes (i%8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8*(i/8)+i%8 = i by omega, canonicalLimb_bigEndian_byte value i hi] at h
  exact h

end P256.Proofs.Projective.Multiply.Machine.Radix.Serialize
