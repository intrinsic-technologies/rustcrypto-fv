import K256.Proofs.Common.ScalarWords
import K256.Proofs.ParseSignature.Scalar.Borrow
import K256.Spec.Secp256k1

namespace K256.Proofs.Generate.Sampling

open K256.Proofs.Common K256.Proofs.ParseSignature.Scalar
open Prelude Standards.SECG.ECC Standards.SECG.DomainParameters X86.Machine

def limbsValue (a0 a1 a2 a3 : BitVec 64) : Nat :=
  (a3.toNat * 2^64 + a2.toNat) * 2^128 + a1.toNat * 2^64 + a0.toNat

def orderFlag (a0 a1 a2 a3 : BitVec 64) : BitVec 64 :=
  let c0 := (~~~a0 ||| (0x402da1732fc9bebf#64 + a0)) >>> 63
  let m0 := (0#64 - c0).sshiftRight 63
  let s1 := 0x4551231950b75fc5#64 + a1 + m0
  let c1 := (~~~a1 ||| s1) >>> 63
  let m1 := (0#64 - c1).sshiftRight 63
  let s2 := m1 + a2 + 2#64
  let c2 := (s2 ||| ~~~a2) >>> 63
  let s3 := (0#64 - c2).sshiftRight 63 + a3 + 1#64
  (~~~a3 ||| s3) >>> 63

private theorem topWord_add (a c : BitVec 64) (hc : c = 0 ∨ c = 1) :
    (0#64 - c).sshiftRight 63 + a + 1#64 = ((c - 1#64) >>> 63) + a := by
  rcases hc with rfl | rfl
  · change 0#64 + a + 1#64 = 1#64 + a
    rw [BitVec.zero_add, BitVec.add_comm]
  · change 0xffffffffffffffff#64 + a + 1#64 = 0#64 + a
    rw [BitVec.add_comm (0xffffffffffffffff#64) a, BitVec.add_assoc]
    rw [show 0xffffffffffffffff#64 + 1#64 = 0#64 by decide +kernel,
      BitVec.add_zero, BitVec.zero_add]

private theorem shr63_cases (word : BitVec 64) : word >>> 63 = 0 ∨ word >>> 63 = 1 := by
  have hword := word.isLt
  have hbit : (word >>> 63).toNat < 2 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rcases show (word >>> 63).toNat = 0 ∨ (word >>> 63).toNat = 1 by omega with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

theorem orderFlag_eq (a0 a1 a2 a3 : BitVec 64) :
    orderFlag a0 a1 a2 a3 =
      if limbsValue a0 a1 a2 a3 < Secp256k1.domain.n then 1 else 0 := by
  rw [limbsValue, ← borrowChain_eq a0 a1 a2 a3]
  simp only [orderFlag, borrowChain]
  congr 2
  exact topWord_add _ _ (shr63_cases _)

theorem limbsValue_eq_zero_iff (a0 a1 a2 a3 : BitVec 64) :
    limbsValue a0 a1 a2 a3 = 0 ↔ a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  constructor
  · intro h
    simp only [limbsValue] at h
    exact ⟨BitVec.eq_of_toNat_eq (by change a0.toNat = 0; omega),
      BitVec.eq_of_toNat_eq (by change a1.toNat = 0; omega),
      BitVec.eq_of_toNat_eq (by change a2.toNat = 0; omega),
      BitVec.eq_of_toNat_eq (by change a3.toNat = 0; omega)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem words_all_zero_iff (w : Nat → BitVec 64) :
    (∀ i < 4, w i = 0) ↔ w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega with rfl | rfl | rfl | rfl
    all_goals assumption

theorem nonzeroFlag_eq_one_iff {w : Nat → BitVec 64} {equal : BitVec 8}
    (hbit : equal = 0 ∨ equal = 1)
    (heq : equal = 1 ↔ ∀ i < 4, w i = 0) :
    (~~~equal &&& 1) = 1 ↔ ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) := by
  rw [← words_all_zero_iff, ← heq]
  rcases hbit with rfl | rfl <;> decide +kernel

theorem decodeSecret_extract_eq {mem : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (hBytes : region.HasBytes mem bytes) {off : Nat} (h : off + 32 ≤ bytes.size) :
    let w := scalarWord mem (BitVec.ofNat 64 (region.start + off))
    Keys.decodeSecret Secp256k1.domain (bytes.extract off (off + 32)) =
      if orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
          ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0)
      then some (limbsValue (w 0) (w 1) (w 2) (w 3))
      else none := by
  have hlen : (Secp256k1.domain.n.log2 + 8) / 8 = 32 := by decide +kernel
  have hsize : (bytes.extract off (off + 32)).size = 32 := by
    rw [ByteArray.size_extract, Nat.min_eq_left h, Nat.add_sub_cancel_left]
  let w := scalarWord mem (BitVec.ofNat 64 (region.start + off))
  have hv : Encoding.octetsToNat (bytes.extract off (off + 32)) =
      limbsValue (w 0) (w 1) (w 2) (w 3) :=
    octetsToNat_extract_eq_words hBytes h
  change _ = if orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
    ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) then some (limbsValue (w 0) (w 1) (w 2) (w 3)) else none
  simp only [orderFlag_eq, ← limbsValue_eq_zero_iff]
  by_cases ho : limbsValue (w 0) (w 1) (w 2) (w 3) < Secp256k1.domain.n <;>
    by_cases hz : limbsValue (w 0) (w 1) (w 2) (w 3) = 0 <;>
    simp [Keys.decodeSecret, hlen, hsize, hv, ho, hz, Nat.pos_iff_ne_zero]

theorem decodeSecret_eq_words {mem : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (hBytes : region.HasBytes mem bytes) (hsize : bytes.size = 32) :
    let w := scalarWord mem (BitVec.ofNat 64 region.start)
    Keys.decodeSecret Secp256k1.domain bytes =
      if orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
          ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0)
      then some (limbsValue (w 0) (w 1) (w 2) (w 3))
      else none := by
  have h := decodeSecret_extract_eq hBytes (off := 0) (by omega)
  simpa only [Nat.zero_add, Nat.add_zero, ← hsize, ByteArray.extract_zero_size] using h

end K256.Proofs.Generate.Sampling
