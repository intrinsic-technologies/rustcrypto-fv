import Sha2.Proofs.FIPS180.Parsing
import Sha2.Proofs.FIPS180.Serialization

namespace Sha2.Proofs.FIPS180
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA256

theorem foldl_range_getElem {α β : Type} [Inhabited α] (a : Array α) (f : β → α → β) (b : β) :
    (List.range a.size).foldl (fun b i => f b a[i]!) b = a.foldl f b := by
  have hm : (List.range a.size).map (fun i => a[i]!) = a.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hi₀ : i < a.size := by simpa using hi'
      simp [hi₀]
  rw [← List.foldl_map, hm, Array.foldl_toList]

theorem compress_foldl_parse (input : Array Bool) (H : Vector (BitVec 32) 8) :
    (List.range (input.size / 512)).foldl
      (fun hash i => NIST.SHA256.compress hash (input.extract (512*i) (512*(i+1))))
      (H.toArray.map UInt32.ofBitVec) =
    (SHA256.hashComputation (SHA256.parse input) H).toArray.map UInt32.ofBitVec := by
  have h (indices : List Nat) (hbound : ∀ i ∈ indices, i < input.size / 512)
      (H : Vector (BitVec 32) 8) :
      indices.foldl
        (fun hash i => NIST.SHA256.compress hash (input.extract (512*i) (512*(i+1))))
        (H.toArray.map UInt32.ofBitVec) =
      (indices.foldl (fun hash i => SHA256.hashBlock hash (SHA256.parse input)[i]!) H).toArray.map
        UInt32.ofBitVec := by
    induction indices generalizing H with
    | nil => rfl
    | cons i indices ih =>
      have hi := hbound i (by simp)
      have hip : i < (SHA256.parse input).size := by simpa only [SHA256.parse, Array.size_ofFn] using hi
      simp only [List.foldl_cons, getElem!_pos (SHA256.parse input) i hip]
      rw [compress_eq_hashBlock_words H _ ((SHA256.parse input)[i])
        (initialSchedule_parse input i hi)]
      exact ih (fun j hj => hbound j (by simp [hj])) _
  have hp : (SHA256.parse input).size = input.size / 512 := by simp [SHA256.parse]
  rw [h _ (fun i hi => List.mem_range.mp hi), ← hp, foldl_range_getElem]
  rfl

theorem initialHash_eq :
    NIST.SHA256.initialHash = SHA256.«H⁽⁰⁾».toArray.map UInt32.ofBitVec := by
  decide +kernel

theorem sha256Bits_eq_fips180 (input : Array Bool) :
    (NIST.SHA256.sha256Bits input).data = (Standards.NIST.SHA2.SHA256 input).bytes.toArray := by
  have hbits : NIST.SHA256.sha256Bits input =
      serializeHash ((List.range ((NIST.SHA256.pad input).size / 512)).foldl
        (fun hash i => NIST.SHA256.compress hash
          ((NIST.SHA256.pad input).extract (512*i) (512*(i+1)))) NIST.SHA256.initialHash) := by
    unfold NIST.SHA256.sha256Bits
    change Id.run (do
      let hash ← forIn ([:(NIST.SHA256.pad input).size / 512] : Std.Legacy.Range)
        NIST.SHA256.initialHash (fun i hash => pure (ForInStep.yield
          (NIST.SHA256.compress hash ((NIST.SHA256.pad input).extract (512*i) (512*(i+1))))))
      pure (serializeHash hash)) = _
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Id.run, pure_bind, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    rfl
  rw [hbits, pad_eq, initialHash_eq, compress_foldl_parse, serializeHash_eq_digestOfHash]
  rfl

theorem sha256_eq_fips180 (input : ByteArray) :
    (NIST.SHA256.sha256 input).data =
      (Standards.NIST.SHA2.SHA256 (bytesToBits input)).bytes.toArray := by
  rw [NIST.SHA256.sha256, sha256Bits_eq_fips180, octetsToBits_eq_bytesToBits]

theorem initialHash224_eq :
    NIST.SHA256.initialHash224 = SHA224.«H⁽⁰⁾».toArray.map UInt32.ofBitVec := by
  decide +kernel

theorem digestOfHash_extract (H : Vector (BitVec 32) 8) (n : Nat) (hn : n ≤ 32) :
    (digestOfHash H).bytes.toArray.extract 0 n =
      (Digest.ofBits (Vector.ofFn (n := 8 * n) fun j =>
        (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))).bytes.toArray := by
  apply Array.ext
  · simp [hn]
  · intro i hi hi'
    simp only [Array.getElem_extract, Nat.zero_add, Vector.getElem_toArray]
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_getMsbD_eq
    intro j hj
    simp only [digestOfHash, Digest.ofBits, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec]

theorem truncatedBits_eq_fips180 (H : Vector (BitVec 32) 8) (n : Nat) (hn : n ≤ 32)
    (input : Array Bool) :
    (NIST.SHA256.truncatedBits (H.toArray.map UInt32.ofBitVec) n input).data =
      (Digest.ofBits (Vector.ofFn (n := 8 * n) fun j =>
        ((SHA256.hashComputation (SHA256.parse (SHA256.pad input)) H)[j.val / 32]'(by omega)).getMsbD
          (j.val % 32))).bytes.toArray := by
  change ((serializeHash ((List.range ((NIST.SHA256.pad input).size / 512)).foldl
    (fun hash i => NIST.SHA256.compress hash
      ((NIST.SHA256.pad input).extract (512*i) (512*(i+1))))
      (H.toArray.map UInt32.ofBitVec))).extract 0 n).data = _
  rw [pad_eq, compress_foldl_parse, ByteArray.data_extract,
    serializeHash_eq_digestOfHash, digestOfHash_extract _ n hn]

theorem sha224_eq_fips180 (input : ByteArray) :
    (NIST.SHA256.sha224 input).data =
      (Standards.NIST.SHA2.SHA224 (bytesToBits input)).bytes.toArray := by
  unfold NIST.SHA256.sha224
  rw [initialHash224_eq, truncatedBits_eq_fips180 _ 28 (by decide),
    octetsToBits_eq_bytesToBits]
  rfl

end Sha2.Proofs.FIPS180
