import P256.Proofs.Program.Output
import P256.Proofs.ReadBe.Input
import P256.Proofs.SignatureFromDer.Model

set_option autoImplicit false

namespace P256.Proofs.SignatureWrapper.Epilogue.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.SecretKeyFromBytes.Encoding
open Standards.SECG.ECC

theorem bytes_natToOctets {s : RamState} {address : BitVec 64} {value : Nat}
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 4, memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      bswap64 (BitVec.ofNat 64 (value / 2^(64*(3-j))))) :
    ∀ i < 32, s.external[address + BitVec.ofNat 64 i]? =
      some (Encoding.natToOctets 32 value).data[i]! := by
  intro i hi
  have hj : i / 8 < 4 := by omega
  have hb := Bytes.of_memLoad (n := 64) (m := s.external)
    (a := address + BitVec.ofNat 64 (8*(i/8))) (by
      intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  rw [words (i/8) hj] at hb
  have hbyte := hb (i%8) (by omega)
  have index : 8*(i/8)+i%8 = i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, index] at hbyte
  rw [hbyte]
  congr 1
  rw [storedByte_eq_extract, bswap64_byte _ _ (by omega), ← storedByte_eq_extract,
    P256.Proofs.ReadBe.storedByte_ofNat64 _ _ (by omega)]
  rw [getElem!_pos _ i (by simpa only [ByteArray.size_data, natToOctets_size] using hi),
    natToOctets_getElem _ _ _ hi, Nat.div_div_eq_div_mul]
  have power : 2^(64*(3-i/8))*256^(7-i%8) = 256^(32-1-i) := by
    rw [show (256:Nat)=2^8 by decide +kernel, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  rw [power]

theorem bytes_encodeFixed {s : RamState} {address : BitVec 64} {value : Nat × Nat}
    (allocated : ∀ i < 64, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (first : ∀ j < 4, memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      bswap64 (BitVec.ofNat 64 (value.1 / 2^(64*(3-j)))))
    (second : ∀ j < 4, memLoad s.external (address + 32 + BitVec.ofNat 64 (8*j)) 64 =
      bswap64 (BitVec.ofNat 64 (value.2 / 2^(64*(3-j))))) :
    ∀ i < (Ecdsa.encodeFixed value).size, s.external[address + BitVec.ofNat 64 i]? =
      some (Ecdsa.encodeFixed value).data[i]! := by
  have firstBytes := bytes_natToOctets (fun i hi => allocated i (by omega)) first
  have secondBytes := bytes_natToOctets (address := address + 32) (by
    intro i hi
    change (s.external[address + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]?).isSome
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact allocated (32+i) (by omega)) second
  intro i hi
  rw [P256.Proofs.SignatureFromDer.encodeFixed_size] at hi
  change _ = some ((Encoding.natToOctets 32 value.1 ++ Encoding.natToOctets 32 value.2).data[i]!)
  rw [ByteArray.data_append, getElem!_pos _ i (by
    simp only [Array.size_append, ByteArray.size_data, natToOctets_size]; omega)]
  by_cases left : i < 32
  · rw [Array.getElem_append_left (by simpa only [ByteArray.size_data, natToOctets_size] using left)]
    simpa only [getElem!_pos (Encoding.natToOctets 32 value.1).data i (by simpa only [ByteArray.size_data, natToOctets_size] using left)] using firstBytes i left
  · rw [Array.getElem_append_right (by simp only [ByteArray.size_data, natToOctets_size]; omega)]
    simp only [ByteArray.size_data, natToOctets_size]
    have h := secondBytes (i-32) (by omega)
    change s.external[address + BitVec.ofNat 64 32 + BitVec.ofNat 64 (i-32)]? = _ at h
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32+(i-32)=i by omega] at h
    simpa only [getElem!_pos (Encoding.natToOctets 32 value.2).data (i-32) (by simp only [ByteArray.size_data, natToOctets_size]; omega)] using h

end P256.Proofs.SignatureWrapper.Epilogue.Success
