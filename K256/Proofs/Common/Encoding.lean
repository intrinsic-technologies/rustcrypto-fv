import Standards.SECG.ECC.Encoding

set_option autoImplicit false

namespace K256.Proofs.Common.Encoding

open Standards.SECG.ECC.Encoding

theorem natToOctets_size (length value : Nat) : (natToOctets length value).size = length := by
  change (Array.map _ (Array.range length)).size = length
  rw [Array.size_map, Array.size_range]

theorem natToOctets_getElem (length value i : Nat) (hi : i < length) :
    (natToOctets length value).data[i]'(by simpa only [ByteArray.size_data,
      natToOctets_size] using hi) =
      UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256) := by
  simp [natToOctets]

theorem natToOctets_succ (length value : Nat) :
    natToOctets (length + 1) value =
      natToOctets length (value / 256) ++ ⟨#[UInt8.ofNat (value % 256)]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, ByteArray.size_append, natToOctets_size]
    rfl
  · intro i hi hj
    simp only [ByteArray.data_append] at hj ⊢
    have hil : i < length + 1 := by
      simpa only [ByteArray.size_data, natToOctets_size] using hi
    by_cases h : i < length
    · rw [Array.getElem_append_left (by simpa only [ByteArray.size_data,
        natToOctets_size] using h)]
      rw [natToOctets_getElem _ _ _ hil, natToOctets_getElem _ _ _ h]
      have he : length + 1 - 1 - i = (length - 1 - i) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 256]
    · have he : i = length := by omega
      subst i
      rw [Array.getElem_append_right (by simp only [ByteArray.size_data,
        natToOctets_size, Nat.le_refl])]
      simp [natToOctets_getElem _ _ _ hil, ByteArray.size_data, natToOctets_size]

theorem natToOctets_octetsToNat (input : ByteArray) :
    natToOctets input.size (octetsToNat input) = input := by
  rcases input with ⟨data⟩
  rcases data with ⟨items⟩
  generalize hr : items.reverse = rev
  have he : items = rev.reverse := by rw [← hr, List.reverse_reverse]
  subst items
  clear hr
  induction rev with
  | nil => simp [natToOctets, octetsToNat, ByteArray.size]
  | cons byte rev ih =>
    let data := rev.reverse.toArray
    simp only [List.reverse_cons]
    have hpush : (⟨rev.reverse ++ [byte]⟩ : Array UInt8) = data.push byte := by
      apply Array.toList_inj.mp
      simp [data]
    rw [hpush]
    change natToOctets data.size (octetsToNat ⟨data⟩) = ⟨data⟩ at ih
    have hb := byte.toNat_lt
    simp only [ByteArray.size, Array.size_push]
    change natToOctets (data.size + 1) (octetsToNat ⟨data.push byte⟩) = _
    have hp : octetsToNat ⟨data.push byte⟩ =
        256 * octetsToNat ⟨data⟩ + byte.toNat := by
      simp only [octetsToNat, Array.foldl_push]
    rw [hp, natToOctets_succ]
    have hd : (256 * octetsToNat ⟨data⟩ + byte.toNat) / 256 = octetsToNat ⟨data⟩ := by
      omega
    have hm : (256 * octetsToNat ⟨data⟩ + byte.toNat) % 256 = byte.toNat := by
      omega
    rw [hd, hm, UInt8.ofNat_toNat, ih]
    apply ByteArray.ext
    simp [ByteArray.data_append]

end K256.Proofs.Common.Encoding
