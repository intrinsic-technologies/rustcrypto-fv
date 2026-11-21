import Sha2.Proofs.FIPS180.Parsing512
import Sha2.Proofs.FIPS180.Serialization512

namespace Sha2.Proofs.FIPS180
namespace SHA512Bridge
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA512

theorem foldl_range_getElem {α β : Type} [Inhabited α] (a : Array α) (f : β → α → β) (b : β) :
    (List.range a.size).foldl (fun b i => f b a[i]!) b = a.foldl f b := by
  have hm : (List.range a.size).map (fun i => a[i]!) = a.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hi₀ : i < a.size := by simpa using hi'
      simp [hi₀]
  rw [← List.foldl_map, hm, Array.foldl_toList]

theorem compress_foldl_parse (input : Array Bool) (H : Vector (BitVec 64) 8) :
    (List.range (input.size / 1024)).foldl
      (fun hash i => NIST.SHA512.compress hash (input.extract (1024*i) (1024*(i+1))))
      (H.toArray.map UInt64.ofBitVec) =
    (SHA512.hashComputation (SHA512.parse input) H).toArray.map UInt64.ofBitVec := by
  have h (indices : List Nat) (hbound : ∀ i ∈ indices, i < input.size / 1024)
      (H : Vector (BitVec 64) 8) :
      indices.foldl
        (fun hash i => NIST.SHA512.compress hash (input.extract (1024*i) (1024*(i+1))))
        (H.toArray.map UInt64.ofBitVec) =
      (indices.foldl (fun hash i => SHA512.hashBlock hash (SHA512.parse input)[i]!) H).toArray.map
        UInt64.ofBitVec := by
    induction indices generalizing H with
    | nil => rfl
    | cons i indices ih =>
      have hi := hbound i (by simp)
      have hip : i < (SHA512.parse input).size := by simpa only [SHA512.parse, Array.size_ofFn] using hi
      simp only [List.foldl_cons, getElem!_pos (SHA512.parse input) i hip]
      rw [compress_eq_hashBlock_words H _ ((SHA512.parse input)[i])
        (initialSchedule_parse input i hi)]
      exact ih (fun j hj => hbound j (by simp [hj])) _
  have hp : (SHA512.parse input).size = input.size / 1024 := by simp [SHA512.parse]
  rw [h _ (fun i hi => List.mem_range.mp hi), ← hp, foldl_range_getElem]
  rfl

theorem initialHash_eq :
    NIST.SHA512.initialHash = SHA512.«H⁽⁰⁾».toArray.map UInt64.ofBitVec := by
  decide +kernel

theorem initialHash384_eq :
    NIST.SHA512.initialHash384 = SHA384.«H⁽⁰⁾».toArray.map UInt64.ofBitVec := by
  decide +kernel

theorem pad_eq512 (input : Array Bool) :
    NIST.SHA512.pad input = SHA512.pad input := by
  unfold NIST.SHA512.pad SHA512.pad
  apply congrArg (fun tail : Array Bool => input ++ #[true] ++
    Array.replicate ((896 + 1024 - (input.size + 1) % 1024) % 1024) false ++ tail)
  apply Array.ext
  · simp [wordToBits]
  · intro i hi hi'
    have hi128 : i < 128 := by simpa using hi'
    simp [wordToBits, BitVec.getMsbD, BitVec.getLsbD_ofNat,
      show 127-i < 128 by omega]

theorem sha512Bits_eq_fips180 (input : Array Bool) :
    (NIST.SHA512.sha512Bits input).data = (Standards.NIST.SHA2.SHA512 input).bytes.toArray := by
  have hbits : NIST.SHA512.sha512Bits input =
      serializeHash ((List.range ((NIST.SHA512.pad input).size / 1024)).foldl
        (fun hash i => NIST.SHA512.compress hash
          ((NIST.SHA512.pad input).extract (1024*i) (1024*(i+1)))) NIST.SHA512.initialHash) := by
    unfold NIST.SHA512.sha512Bits
    change Id.run (do
      let hash ← forIn ([:(NIST.SHA512.pad input).size / 1024] : Std.Legacy.Range)
        NIST.SHA512.initialHash (fun i hash => pure (ForInStep.yield
          (NIST.SHA512.compress hash ((NIST.SHA512.pad input).extract (1024*i) (1024*(i+1))))))
      pure (serializeHash hash)) = _
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Id.run, pure_bind, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    rfl
  rw [hbits, pad_eq512, initialHash_eq, compress_foldl_parse, serializeHash_eq_digestOfHash]
  rfl

theorem sha512_eq_fips180 (input : ByteArray) :
    (NIST.SHA512.sha512 input).data =
      (Standards.NIST.SHA2.SHA512 (bytesToBits input)).bytes.toArray := by
  rw [NIST.SHA512.sha512, sha512Bits_eq_fips180, octetsToBits_eq_bytesToBits]

theorem sha384Bits_eq_fips180 (input : Array Bool) :
    (NIST.SHA512.sha384Bits input).data = (Standards.NIST.SHA2.SHA384 input).bytes.toArray := by
  have hbits : NIST.SHA512.sha384Bits input =
      serializeHash (((List.range ((NIST.SHA512.pad input).size / 1024)).foldl
        (fun hash i => NIST.SHA512.compress hash
          ((NIST.SHA512.pad input).extract (1024*i) (1024*(i+1)))) NIST.SHA512.initialHash384).extract 0 6) := by
    unfold NIST.SHA512.sha384Bits
    change Id.run (do
      let hash ← forIn ([:(NIST.SHA512.pad input).size / 1024] : Std.Legacy.Range)
        NIST.SHA512.initialHash384 (fun i hash => pure (ForInStep.yield
          (NIST.SHA512.compress hash ((NIST.SHA512.pad input).extract (1024*i) (1024*(i+1))))))
      pure (serializeHash (hash.extract 0 6))) = _
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Id.run, pure_bind, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      ← List.range_eq_range']
    rfl
  rw [hbits, pad_eq512, initialHash384_eq, compress_foldl_parse,
    serializeHash_extract6_eq_digestOfHash384]
  rfl

theorem sha384_eq_fips180 (input : ByteArray) :
    (NIST.SHA512.sha384 input).data =
      (Standards.NIST.SHA2.SHA384 (bytesToBits input)).bytes.toArray := by
  rw [NIST.SHA512.sha384, sha384Bits_eq_fips180, octetsToBits_eq_bytesToBits]

theorem initialHash224_eq :
    NIST.SHA512.initialHash224 = SHA512_224.«H⁽⁰⁾».toArray.map UInt64.ofBitVec := by
  decide +kernel

theorem initialHash256_eq :
    NIST.SHA512.initialHash256 = SHA512_256.«H⁽⁰⁾».toArray.map UInt64.ofBitVec := by
  decide +kernel

theorem digestOfHash_extract (H : Vector (BitVec 64) 8) (n : Nat) (hn : n ≤ 64) :
    (digestOfHash H).bytes.toArray.extract 0 n =
      (Digest.ofBits (Vector.ofFn (n := 8 * n) fun j =>
        (H[j.val / 64]'(by omega)).getMsbD (j.val % 64))).bytes.toArray := by
  apply Array.ext
  · simp [hn]
  · intro i hi hi'
    simp only [Array.getElem_extract, Nat.zero_add, Vector.getElem_toArray]
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_getMsbD_eq
    intro j hj
    simp only [digestOfHash, Digest.ofBits, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec]

theorem truncatedBits_eq_fips180 (H : Vector (BitVec 64) 8) (n : Nat) (hn : n ≤ 64)
    (input : Array Bool) :
    (NIST.SHA512.truncatedBits (H.toArray.map UInt64.ofBitVec) n input).data =
      (Digest.ofBits (Vector.ofFn (n := 8 * n) fun j =>
        ((SHA512.hashComputation (SHA512.parse (SHA512.pad input)) H)[j.val / 64]'(by omega)).getMsbD
          (j.val % 64))).bytes.toArray := by
  change ((serializeHash ((List.range ((NIST.SHA512.pad input).size / 1024)).foldl
    (fun hash i => NIST.SHA512.compress hash
      ((NIST.SHA512.pad input).extract (1024*i) (1024*(i+1))))
      (H.toArray.map UInt64.ofBitVec))).extract 0 n).data = _
  rw [pad_eq512, compress_foldl_parse, ByteArray.data_extract,
    serializeHash_eq_digestOfHash, digestOfHash_extract _ n hn]

theorem sha512_224_eq_fips180 (input : ByteArray) :
    (NIST.SHA512.sha512_224 input).data =
      (Standards.NIST.SHA2.SHA512_224 (bytesToBits input)).bytes.toArray := by
  unfold NIST.SHA512.sha512_224
  rw [initialHash224_eq, truncatedBits_eq_fips180 _ 28 (by decide),
    octetsToBits_eq_bytesToBits]
  rfl

theorem sha512_256_eq_fips180 (input : ByteArray) :
    (NIST.SHA512.sha512_256 input).data =
      (Standards.NIST.SHA2.SHA512_256 (bytesToBits input)).bytes.toArray := by
  unfold NIST.SHA512.sha512_256
  rw [initialHash256_eq, truncatedBits_eq_fips180 _ 32 (by decide),
    octetsToBits_eq_bytesToBits]
  rfl

end SHA512Bridge
end Sha2.Proofs.FIPS180
