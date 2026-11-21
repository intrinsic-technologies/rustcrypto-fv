import Standards.SECG.ECC.Encoding
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Encoding

open Standards.SECG.ECC.Encoding

theorem natToOctets_size (length value : Nat) :
    (natToOctets length value).size = length := by
  simp [natToOctets, ByteArray.size]

theorem natToOctets_getElem (length value i : Nat) (hi : i < length) :
    (natToOctets length value).data[i]'(by simpa only [ByteArray.size_data,
      natToOctets_size] using hi) =
      UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256) := by
  simp [natToOctets]

theorem natToOctets_getElem? (length value i : Nat) (hi : i < length) :
    (natToOctets length value).data[i]? =
      some (UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256)) := by
  simp [natToOctets, hi]

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

theorem octetsToNat_lt (input : ByteArray) : octetsToNat input < 256 ^ input.size := by
  rcases input with ⟨data⟩
  rcases data with ⟨items⟩
  generalize hr : items.reverse = rev
  have he : items = rev.reverse := by rw [← hr, List.reverse_reverse]
  subst items
  clear hr
  induction rev with
  | nil => decide +kernel
  | cons byte rev ih =>
    let data := rev.reverse.toArray
    simp only [List.reverse_cons]
    have hpush : (⟨rev.reverse ++ [byte]⟩ : Array UInt8) = data.push byte := by
      apply Array.toList_inj.mp
      simp [data]
    rw [hpush]
    change octetsToNat ⟨data⟩ < 256 ^ (ByteArray.size ⟨data⟩) at ih
    have hb := byte.toNat_lt
    simp only [ByteArray.size, Array.size_push]
    change (data.push byte).foldl (fun v b => 256*v+b.toNat) 0 < 256^(data.size+1)
    rw [Array.foldl_push, Nat.pow_succ]
    change 256 * octetsToNat ⟨data⟩ + byte.toNat < 256 ^ (ByteArray.size ⟨data⟩) * 256
    omega

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
    change natToOctets (data.size+1) (octetsToNat ⟨data.push byte⟩) = _
    have hp : octetsToNat ⟨data.push byte⟩ = 256 * octetsToNat ⟨data⟩ + byte.toNat := by
      simp only [octetsToNat, Array.foldl_push]
    rw [hp, natToOctets_succ]
    have hd : (256*octetsToNat ⟨data⟩+byte.toNat)/256 = octetsToNat ⟨data⟩ := by omega
    have hm : (256*octetsToNat ⟨data⟩+byte.toNat)%256 = byte.toNat := by omega
    rw [hd, hm, UInt8.ofNat_toNat, ih]
    apply ByteArray.ext
    simp [ByteArray.data_append]

theorem octetsToNat_byte (input : ByteArray) (i : Nat) (hi : i < input.size) :
    input.data[i] = UInt8.ofNat (octetsToNat input / 256^(input.size-1-i) % 256) := by
  have h := natToOctets_getElem? input.size (octetsToNat input) i hi
  rw [natToOctets_octetsToNat] at h
  simpa only [Array.getElem?_eq_getElem hi, Option.some.injEq] using h

end P256.Proofs.SecretKeyFromBytes.Encoding
