import Sha3.Proofs.Incremental.Basic
import Sha3.Proofs.Incremental.Canonical.Blocks
import Sha3.Proofs.Incremental.Canonical.Byte

namespace Sha3.Proofs.Incremental

open Keccak Absorption

theorem absorbByte_canonicalState (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (bytes : ByteArray) (byte : UInt8) :
    absorbByte permute rate (canonicalState permute rate bytes) byte =
      canonicalState permute rate (bytes.push byte) := by
  have hmod := Nat.mod_lt bytes.size hr
  have hdiv := Nat.div_add_mod bytes.size rate
  rw [Nat.mul_comm rate] at hdiv
  by_cases hfull : bytes.size % rate + 1 = rate
  · have hlen : bytes.size + 1 = (bytes.size / rate + 1) * rate := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hquot : (bytes.push byte).size / rate = bytes.size / rate + 1 := by
      rw [ByteArray.size_push, hlen, Nat.mul_div_cancel _ hr]
    have hcursor : (bytes.push byte).size % rate = 0 := by
      rw [ByteArray.size_push, hlen]
      simp
    have hzero := blockLanes_eq_zero_of_size_le (bytes.push byte)
      ((bytes.push byte).size / rate * rate) rate (by
        rw [hquot, ByteArray.size_push, hlen]
        exact Nat.le_refl _)
    simp only [absorbByte, canonicalState, hfull, ↓reduceIte,
      absorbBlocks_push_of_mod_eq permute rate hr bytes byte hfull, hzero,
      BitVec.xor_zero, blockLanes_push_remainder bytes byte rate hr, BitVec.xor_assoc,
      hcursor]
  · have hquot : (bytes.push byte).size / rate = bytes.size / rate := by
      rw [ByteArray.size_push]
      apply Nat.div_eq_of_lt_le
      · omega
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
    have hcursor : (bytes.push byte).size % rate = bytes.size % rate + 1 := by
      have hdiv' := Nat.div_add_mod (bytes.push byte).size rate
      rw [hquot, Nat.mul_comm rate, ByteArray.size_push] at hdiv'
      rw [ByteArray.size_push]
      omega
    simp only [absorbByte, canonicalState, hfull, ↓reduceIte,
      absorbBlocks_push_of_mod_ne permute rate hr bytes byte hfull, hquot,
      blockLanes_push_remainder bytes byte rate hr, BitVec.xor_assoc, hcursor]

theorem update_canonicalState (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (prior bytes : ByteArray) :
    update permute rate (canonicalState permute rate prior) bytes =
      canonicalState permute rate (prior ++ bytes) := by
  cases bytes with
  | mk data =>
    cases data with
    | mk values =>
      induction values generalizing prior with
      | nil =>
        have hempty : ByteArray.mk #[] = ByteArray.empty := by
          apply ByteArray.ext
          simp
        change update permute rate (canonicalState permute rate prior) (ByteArray.mk #[]) = _
        rw [hempty, update_empty, ByteArray.append_empty]
      | cons byte values ih =>
        have hsplit : ByteArray.mk (byte :: values).toArray =
            ByteArray.empty.push byte ++ ByteArray.mk values.toArray := by
          apply ByteArray.ext
          simp [ByteArray.data_append, ByteArray.data_push]
        rw [hsplit, update_append, update_push, update_empty,
          absorbByte_canonicalState permute rate hr, ih]
        congr 1
        apply ByteArray.ext
        simp [ByteArray.data_push, ByteArray.data_append]

theorem update_initial (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (bytes : ByteArray) :
    update permute rate initial bytes = canonicalState permute rate bytes := by
  simpa only [canonicalState_empty, ByteArray.empty_append] using
    update_canonicalState permute rate hr ByteArray.empty bytes

end Sha3.Proofs.Incremental
