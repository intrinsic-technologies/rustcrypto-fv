import Standards.NIST.SHA3.Digest
import Standards.NIST.SHA3

namespace Sha3.Proofs

open Standards.NIST.SHA3

theorem getLsbD_digest_ofBits {n : Nat} (bits : Vector Bool (8 * n))
    (i j : Nat) (hi : i < n) (hj : j < 8) :
    (Digest.ofBits bits)[i].toBitVec.getLsbD j = bits[8 * i + j] := by
  simp only [Digest.ofBits, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec,
    BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]

theorem size_bytesToBits (bs : ByteArray) : (bytesToBits bs).size = 8 * bs.size := by
  simp only [bytesToBits, Array.size_flatMap, Array.size_map, Array.size_range,
    Array.map_const', Array.sum_replicate_nat, ByteArray.size]
  omega

theorem bytesToBits_append (a b : ByteArray) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits]

theorem getElem_bytesToBits (bs : ByteArray) (i : Nat) (h : i < 8 * bs.size) :
    (bytesToBits bs)[i]'(by rw [size_bytesToBits]; exact h) =
      (bs.data[i / 8]'(by change i / 8 < bs.size; omega)).toBitVec.getLsbD (i % 8) := by
  rcases bs with ⟨⟨xs⟩⟩
  induction xs generalizing i with
  | nil => simp [ByteArray.size] at h
  | cons x xs ih =>
    simp only [bytesToBits, List.flatMap_toArray_cons]
    by_cases hi : i < 8
    · rw [Array.getElem_append_left (by simpa using hi)]
      simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · rw [Array.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
      have ht : i - 8 < 8 * (ByteArray.mk xs.toArray).size := by
        simp only [ByteArray.size, List.size_toArray, List.length_cons] at h ⊢
        omega
      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
      have hmod : i % 8 = (i - 8) % 8 := by omega
      simpa only [bytesToBits, Array.size_map, Array.size_range, hdiv, hmod,
        List.getElem_toArray, List.getElem_cons_succ] using ih (i - 8) ht

theorem bytesToBits_eq_ofFn (bs : ByteArray) :
    bytesToBits bs = Array.ofFn (fun i : Fin (8 * bs.size) ↦
      (bs.data[i.val / 8]'(by change i.val / 8 < bs.size; omega)).toBitVec.getLsbD
        (i.val % 8)) := by
  apply Array.ext
  · simp [size_bytesToBits]
  · intro i hi hj
    simp only [Array.size_ofFn] at hj
    simp only [Array.getElem_ofFn, getElem_bytesToBits bs i hj]

theorem getElem_bytesToBits_byte (bs : ByteArray) (i j : Nat)
    (hi : i < bs.size) (hj : j < 8) :
    (bytesToBits bs)[8 * i + j]'(by rw [size_bytesToBits]; omega) =
      (bs.data[i]'hi).toBitVec.getLsbD j := by
  rw [getElem_bytesToBits bs (8 * i + j) (by omega)]
  have hdiv : (8 * i + j) / 8 = i := by omega
  have hmod : (8 * i + j) % 8 = j := by omega
  simp only [hdiv, hmod]

theorem bytesToBits_injective {a b : ByteArray} (h : bytesToBits a = bytesToBits b) :
    a = b := by
  have hs : a.size = b.size := by
    have := congrArg Array.size h
    simp only [size_bytesToBits] at this
    omega
  apply ByteArray.ext
  apply Array.ext
  · exact hs
  · intro i hi hj
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hbit
    rw [← getElem_bytesToBits_byte a i j hi hbit,
      ← getElem_bytesToBits_byte b i j hj hbit]
    congr 1

theorem bytesToBits_extract (bs : ByteArray) (start stop : Nat) :
    bytesToBits (bs.extract start stop) = (bytesToBits bs).extract (8 * start) (8 * stop) := by
  apply Array.ext
  · simp only [size_bytesToBits, ByteArray.size_extract, Array.size_extract]
    omega
  · intro i hi hj
    have hb : i < 8 * (bs.extract start stop).size := by
      simpa only [size_bytesToBits] using hi
    rw [getElem_bytesToBits _ i hb]
    simp only [ByteArray.data_extract, Array.getElem_extract]
    rw [getElem_bytesToBits _ (8 * start + i) (by
      simp only [Array.size_extract, size_bytesToBits] at hj
      omega)]
    have hdiv : (8 * start + i) / 8 = start + i / 8 := by omega
    have hmod : (8 * start + i) % 8 = i % 8 := by omega
    simp only [hdiv, hmod]

theorem bytesToBits_xor (a b : ByteArray) :
    bytesToBits ⟨a.data.zipWith (· ^^^ ·) b.data⟩ =
      (bytesToBits a).zipWith (· ^^ ·) (bytesToBits b) := by
  apply Array.ext
  · simp only [size_bytesToBits, ByteArray.size, Array.size_zipWith]
    omega
  · intro i hi hj
    have ha : i < 8 * a.size := by
      simp only [Array.size_zipWith, size_bytesToBits] at hj
      omega
    have hb : i < 8 * b.size := by
      simp only [Array.size_zipWith, size_bytesToBits] at hj
      omega
    rw [getElem_bytesToBits _ i (by simpa only [size_bytesToBits] using hi)]
    simp only [Array.getElem_zipWith, getElem_bytesToBits a i ha, getElem_bytesToBits b i hb,
      UInt8.toBitVec_xor, BitVec.getLsbD_xor]

def trunc {b : Nat} (s : Vector Bool b) (n : Nat)
    (h : n ≤ b := by omega) : Vector Bool n :=
  Vector.ofFn fun i ↦ s[(i : Nat)]'(by omega)

theorem squeeze_initial_trunc {b : Nat} (f : Vector Bool b → Vector Bool b)
    (r : Nat) (hr : 0 < r ∧ r < b) (s : Vector Bool b) (d : Nat) (hd : d ≤ r) :
    squeeze f r hr s d = trunc s d (by omega) := by
  apply Vector.ext
  intro i hi
  have hir : i < r := Nat.lt_of_lt_of_le hi hd
  simp only [squeeze, trunc, Vector.getElem_ofFn, Nat.div_eq_of_lt hir,
    Nat.mod_eq_of_lt hir, Nat.repeat]

theorem sponge_eq_trunc_absorb {b : Nat} (f : Vector Bool b → Vector Bool b)
    (pad : PaddingRule) (r : Nat) (hr : 0 < r ∧ r < b)
    (input : Array Bool) (d : Nat) (hd : d ≤ r) :
    sponge f pad r hr input d = trunc (absorb f pad r hr input) d (by omega) :=
  squeeze_initial_trunc f r hr _ d hd

end Sha3.Proofs

namespace Sha3.Proofs.Padding

theorem pad101_zero_count_suffix (r n k : Nat) (hr : 0 < r) (hk : k ≤ 6) :
    ((-((8 * n + k : Nat) : Int) - 2) % ((8 * r : Nat) : Int)).toNat =
      8 * (r - n % r) - (k + 2) := by
  have hnr := Nat.mod_lt n hr
  have hm : (8 * n : Int) % (8 * r : Int) = 8 * (n % r : Nat) := by
    rw [Int.mul_emod_mul_of_pos _ _ (by decide : (0 : Int) < 8)]
    simp only [Int.natCast_emod]
  have hrem : (-((8 * n + k : Nat) : Int) - 2) % ((8 * r : Nat) : Int) =
      8 * (r : Int) - 8 * (n % r : Nat) - (k : Int) - 2 := by
    change (-(8 * (n : Int) + k) - 2) % (8 * r) = _
    have heq : -(8 * (n : Int) + k) - 2 = -(8 * (n : Int)) - (k : Int) - 2 := by omega
    rw [heq]
    have hm' : (8 * (n : Int)) % (8 * r) = (8 * (n % r : Nat) : Int) % (8 * r) := by
      rw [hm, Int.emod_eq_of_lt] <;> omega
    have hc := (Int.emod_sub_cancel_left (8 * (r : Int) - (k : Int) - 2)).mpr hm'
    have hshift : -(8 * (n : Int)) - (k : Int) - 2 + 8 * (r : Int) =
        8 * (r : Int) - (k : Int) - 2 - 8 * (n : Int) := by omega
    rw [← Int.add_emod_right, hshift, hc]
    rw [Int.emod_eq_of_lt] <;> omega
  rw [hrem]
  omega

theorem pad101_zero_count (r n : Nat) (hr : 0 < r) :
    ((-((8 * n + 2 : Nat) : Int) - 2) % ((8 * r : Nat) : Int)).toNat =
      8 * (r - n % r) - 4 :=
  pad101_zero_count_suffix r n 2 hr (by decide)

theorem sha3_padding_eq (r n : Nat) (hr : 0 < r) :
    #[false, true] ++ Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n + 2) =
      (#[false, true, true] ++ Array.replicate (8 * (r - n % r) - 4) false) ++
        #[true] := by
  simp only [Standards.NIST.SHA3.pad101, pad101_zero_count r n hr, ← Array.append_assoc]
  rfl

theorem size_sha3_padding (r n : Nat) (hr : 0 < r) :
    (#[false, true] ++ Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n + 2)).size =
      8 * (r - n % r) := by
  rw [sha3_padding_eq r n hr]
  simp only [Array.size_append, Array.size_replicate]
  change 3 + (8 * (r - n % r) - 4) + 1 = 8 * (r - n % r)
  have := Nat.mod_lt n hr
  omega

theorem getElem_sha3_padding (r n i : Nat) (hr : 0 < r)
    (hi : i < (#[false, true] ++ Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n + 2)).size) :
    (#[false, true] ++ Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n + 2))[i] =
      decide (i = 1 ∨ i = 2 ∨ i + 1 = 8 * (r - n % r)) := by
  have hd : 0 < r - n % r := by have := Nat.mod_lt n hr; omega
  have hib : i < 8 * (r - n % r) := by rwa [size_sha3_padding r n hr] at hi
  simp only [sha3_padding_eq r n hr]
  by_cases h0 : i = 0
  · subst i
    simp [show ¬1 = 8 * (r - n % r) by omega]
  by_cases h1 : i = 1
  · subst i
    simp
  by_cases h2 : i = 2
  · subst i
    simp
  by_cases hl : i + 1 = 8 * (r - n % r)
  · simp [Array.getElem_append, Array.getElem_push, h1, h2, hl,
      show i - 3 = 8 * (r - n % r) - 4 by omega,
      show ¬i < 3 by omega]
  · simp [Array.getElem_append, Array.getElem_push, h1, h2, hl,
      show i - 3 < 8 * (r - n % r) - 4 by omega,
      show ¬i < 3 by omega]

theorem sha3_paddingByte_bits (first last : Bool) (j : Nat) (hj : j < 8) :
    (((if first then 0x06 else 0) : UInt8) ^^^
      ((if last then 0x80 else 0) : UInt8)).toBitVec.getLsbD j =
        ((first && decide (j = 1 ∨ j = 2)) ^^ (last && decide (j = 7))) := by
  have h : ∀ f l : Bool, ∀ k : Fin 8,
      (((if f then 0x06 else 0) : UInt8) ^^^
        ((if l then 0x80 else 0) : UInt8)).toBitVec.getLsbD k.val =
          ((f && decide (k.val = 1 ∨ k.val = 2)) ^^ (l && decide (k.val = 7))) := by
    decide +kernel
  exact h first last ⟨j, hj⟩

theorem sha3_paddingByte_index_bits (d i : Nat) (hi : i < 8 * d) :
    (((if i / 8 = 0 then 0x06 else 0) : UInt8) ^^^
      ((if i / 8 + 1 = d then 0x80 else 0) : UInt8)).toBitVec.getLsbD (i % 8) =
        decide (i = 1 ∨ i = 2 ∨ i + 1 = 8 * d) := by
  have h := sha3_paddingByte_bits (decide (i / 8 = 0))
    (decide (i / 8 + 1 = d)) (i % 8) (by omega)
  simp only [decide_eq_true_eq] at h
  rw [h]
  apply Bool.eq_iff_iff.mpr
  have hxor : ∀ a b : Bool, (a ^^ b) = true ↔
      (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by decide +kernel
  simp only [hxor, Bool.and_eq_true, Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem sha3_padding_eq_bytesToBits (r n : Nat) (hr : 0 < r) :
    #[false, true] ++ Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n + 2) =
      Standards.NIST.SHA3.bytesToBits ⟨Array.ofFn (fun i : Fin (r - n % r) ↦
        ((if i.val = 0 then 0x06 else 0) : UInt8) ^^^
          ((if i.val + 1 = r - n % r then 0x80 else 0) : UInt8))⟩ := by
  apply Array.ext
  · rw [size_sha3_padding r n hr, size_bytesToBits]
    simp [ByteArray.size]
  · intro i hi hj
    have hib : i < 8 * (r - n % r) := by rwa [size_sha3_padding r n hr] at hi
    rw [getElem_sha3_padding r n i hr hi,
      getElem_bytesToBits _ i (by simpa only [ByteArray.size, Array.size_ofFn] using hib)]
    simp only [Array.getElem_ofFn]
    exact (sha3_paddingByte_index_bits (r - n % r) i hib).symm

theorem sha3_paddedMessage_eq_bytesToBits (r : Nat) (bs : ByteArray) (hr : 0 < r) :
    (Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]) ++
      Standards.NIST.SHA3.pad101.pad (8 * r) (Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]).size =
        Standards.NIST.SHA3.bytesToBits (bs ++ ⟨Array.ofFn (fun i : Fin (r - bs.size % r) ↦
          ((if i.val = 0 then 0x06 else 0) : UInt8) ^^^
            ((if i.val + 1 = r - bs.size % r then 0x80 else 0) : UInt8))⟩) := by
  rw [bytesToBits_append, Array.append_assoc]
  simp only [Array.size_append, size_bytesToBits]
  exact congrArg (Standards.NIST.SHA3.bytesToBits bs ++ ·) (sha3_padding_eq_bytesToBits r bs.size hr)

theorem keccak_padding_eq_bytesToBits (r n : Nat) (hr : 0 < r) :
    Standards.NIST.SHA3.pad101.pad (8 * r) (8 * n) =
      Standards.NIST.SHA3.bytesToBits ⟨Array.ofFn (fun i : Fin (r - n % r) ↦
        ((if i.val = 0 then 0x01 else 0) : UInt8) ^^^
          ((if i.val + 1 = r - n % r then 0x80 else 0) : UInt8))⟩ := by
  have hd : 0 < r - n % r := by have := Nat.mod_lt n hr; omega
  have hz := pad101_zero_count_suffix r n 0 hr (by decide)
  simp only [Nat.add_zero] at hz
  have hbits : ∀ f l : Bool, ∀ k : Fin 8,
      (((if f then 0x01 else 0) : UInt8) ^^^
        ((if l then 0x80 else 0) : UInt8)).toBitVec.getLsbD k.val =
          ((f && decide (k.val = 0)) ^^ (l && decide (k.val = 7))) := by
    decide +kernel
  simp only [Standards.NIST.SHA3.pad101, hz]
  apply Array.ext
  · simp only [Array.size_append, Array.size_replicate, size_bytesToBits,
      ByteArray.size, Array.size_ofFn]
    change 1 + (8 * (r - n % r) - (0 + 2)) + 1 = 8 * (r - n % r)
    omega
  · intro i hi hj
    have hib : i < 8 * (r - n % r) := by
      simpa only [size_bytesToBits, ByteArray.size, Array.size_ofFn] using hj
    rw [getElem_bytesToBits _ i (by
      simpa only [ByteArray.size, Array.size_ofFn] using hib)]
    simp only [Array.getElem_ofFn]
    have hb := hbits (decide (i / 8 = 0))
      (decide (i / 8 + 1 = r - n % r)) ⟨i % 8, by omega⟩
    simp only [decide_eq_true_eq] at hb
    rw [hb]
    by_cases h0 : i = 0
    · subst i
      simp
    by_cases hl : i + 1 = 8 * (r - n % r)
    · have hmod : i % 8 = 7 := by omega
      have hdiv : i / 8 + 1 = r - n % r := by omega
      simp [Array.getElem_append, Array.getElem_push, hmod, hdiv,
        show ¬i < 1 by omega, show i - 1 = 8 * (r - n % r) - 2 by omega]
    · have hf : i < 8 → ¬i % 8 = 0 := by omega
      have he : ¬(i / 8 + 1 = r - n % r ∧ i % 8 = 7) := by omega
      simp only [Nat.zero_add, Array.append_singleton, Array.push_append,
        Array.getElem_append, List.size_toArray, List.length_cons, List.length_nil,
        show ¬i < 1 by omega, ↓reduceDIte, Array.getElem_push, Array.size_replicate,
        show i - 1 < 8 * (r - n % r) - 2 by omega, Array.getElem_replicate,
        Nat.div_eq_zero_iff, reduceCtorEq, false_or, ← Bool.decide_and, he,
        decide_false, Bool.bne_false, false_eq_decide_iff, not_and]
      exact hf

theorem keccak_paddedMessage_eq_bytesToBits (r : Nat) (bs : ByteArray) (hr : 0 < r) :
    Standards.NIST.SHA3.bytesToBits bs ++
      Standards.NIST.SHA3.pad101.pad (8 * r) (Standards.NIST.SHA3.bytesToBits bs).size =
        Standards.NIST.SHA3.bytesToBits (bs ++ ⟨Array.ofFn (fun i : Fin (r - bs.size % r) ↦
          ((if i.val = 0 then 0x01 else 0) : UInt8) ^^^
            ((if i.val + 1 = r - bs.size % r then 0x80 else 0) : UInt8))⟩) := by
  rw [bytesToBits_append, size_bytesToBits, keccak_padding_eq_bytesToBits r bs.size hr]

theorem size_sha3_paddedMessage (r : Nat) (bs : ByteArray) (hr : 0 < r) :
    ((Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]) ++
      Standards.NIST.SHA3.pad101.pad (8 * r) (Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]).size).size =
        8 * r * (bs.size / r + 1) := by
  have hs := size_sha3_padding r bs.size hr
  have hm := Nat.mod_lt bs.size hr
  have hn := Nat.mod_add_div bs.size r
  have htwo : #[false, true].size = 2 := rfl
  simp only [Array.size_append, htwo] at hs
  simp only [Array.size_append, size_bytesToBits, htwo, Nat.mul_assoc, Nat.mul_add,
    Nat.mul_one]
  omega

theorem sha3_paddedMessage_blockCount (r : Nat) (bs : ByteArray) (hr : 0 < r) :
    ((Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]) ++
      Standards.NIST.SHA3.pad101.pad (8 * r) (Standards.NIST.SHA3.bytesToBits bs ++ #[false, true]).size).size /
        (8 * r) = bs.size / r + 1 := by
  rw [size_sha3_paddedMessage r bs hr]
  exact Nat.mul_div_right _ (by omega)

end Sha3.Proofs.Padding
