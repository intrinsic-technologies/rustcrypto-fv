import ChaCha20Poly1305.Proofs.Decrypt.Mac
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Region

namespace ChaCha20Poly1305.Proofs.Decrypt.Bytes
open Standards.RFC.ChaCha20Poly1305 Poly1305 X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine Prelude

def packed (s : ByteArray) : BitVec (8*s.size) := BitVec.ofNat _ (leBytesToNum s)

theorem pow_bytes (k : Nat) : 2^(8*k) = 256^k := Nat.pow_mul _ _ _

theorem packedNat (s : ByteArray) : (packed s).toNat = leBytesToNum s := by
  rw [packed,BitVec.toNat_ofNat,pow_bytes,Nat.mod_eq_of_lt (le_bound _)]

theorem decompose (s : ByteArray) {i : Nat} (hi : i ≤ s.size) :
    leBytesToNum s = leBytesToNum (s.extract 0 i) + 256^i * leBytesToNum (s.extract i s.size) := by
  have h := le_append (s.extract 0 i) (s.extract i s.size)
  rwa [ByteArray.extract_append_extract,Nat.zero_min,Nat.max_eq_right hi,
    ByteArray.extract_zero_size, ByteArray.size_extract,Nat.min_eq_left hi,Nat.sub_zero] at h

theorem upper (s : ByteArray) {i : Nat} (hi : i ≤ s.size) :
    leBytesToNum s / 256^i = leBytesToNum (s.extract i s.size) := by
  have small := le_bound (s.extract 0 i)
  rw [ByteArray.size_extract,Nat.min_eq_left hi,Nat.sub_zero] at small
  rw [decompose s hi,Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt small,Nat.zero_add]

theorem lower (s : ByteArray) {k : Nat} (hk : k ≤ s.size) :
    leBytesToNum s % 256^k = leBytesToNum (s.extract 0 k) := by
  have small := le_bound (s.extract 0 k)
  rw [ByteArray.size_extract,Nat.min_eq_left hk,Nat.sub_zero] at small
  rw [decompose s hk,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

theorem slice (s : ByteArray) (i k : Nat) (h : i+k ≤ s.size) :
    ((packed s).extractLsb' (8*i) (8*k)).toNat = leBytesToNum (s.extract i (i+k)) := by
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,packedNat,pow_bytes]
  rw [upper s (by omega),lower _ (by rw [ByteArray.size_extract]; omega),
    ByteArray.extract_extract,Nat.add_zero,Nat.min_eq_left h]

theorem one (s : ByteArray) {i : Nat} (h : i < s.size) :
    leBytesToNum (s.extract i (i+1)) = s[i].toNat := by
  rw [ByteArray.extract_add_one (by omega)]
  simp only [leBytesToNum]
  rfl

theorem byte (s : ByteArray) {i : Nat} (h : i < s.size) :
    (packed s).extractLsb' (8*i) 8 = s[i].toBitVec := by
  apply BitVec.eq_of_toNat_eq
  exact (slice s i 1 (by omega)).trans (one s h)

theorem mem_packed {m : X86.Machine.Ram} {r : MemoryRegion} {s : ByteArray}
    (h : r.HasBytes m s) : memLoad m (BitVec.ofNat 64 r.start) (8*s.size) = packed s := by
  apply memLoad_eq_of_memByte (by omega)
  intro i hi
  have hlt : i < s.size := by omega
  have atByte := h.2 ⟨i,hlt⟩
  change m[BitVec.ofNat 64 (r.start+i)]? = some s[i] at atByte
  simp only [memByte,PhysicalMemory.read, ← BitVec.ofNat_add,atByte,Option.getD_some]
  change _ = UInt8.ofBitVec ((packed s).extractLsb' (8*i) 8)
  rw [byte]

end ChaCha20Poly1305.Proofs.Decrypt.Bytes
