import Hkdf.Proofs.Common.Model

namespace Hkdf.Proofs.Common.HMAC

open Standards.NIST.SHA2

def keyBlock (key : ByteArray) : ByteArray :=
  let key := if 64 < key.size then SHA256.hashBytes key else key
  key ++ ⟨Array.replicate (64 - key.size) 0⟩

def xorPad (block : ByteArray) (pad : UInt8) : ByteArray :=
  ⟨block.data.map (fun byte ↦ byte ^^^ pad)⟩

theorem sha256_hashBytes_size (input : ByteArray) : (SHA256.hashBytes input).size = 32 := by
  simp only [SHA256.hashBytes, ByteArray.size, Vector.size_toArray]

theorem keyBlock_size (key : ByteArray) : (keyBlock key).size = 64 := by
  have padded_size (bytes : ByteArray) (fits : bytes.size ≤ 64) :
      (bytes ++ ⟨Array.replicate (64 - bytes.size) 0⟩).size = 64 := by
    rw [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate] at fits ⊢
    omega
  unfold keyBlock
  split
  · exact padded_size _ (by rw [sha256_hashBytes_size]; omega)
  · rename_i fits
    exact padded_size _ (by omega)

theorem xorPad_size (block : ByteArray) (pad : UInt8) :
    (xorPad block pad).size = block.size := by
  simp only [xorPad, ByteArray.size, Array.size_map]

theorem keyBlock_idempotent (key : ByteArray) : keyBlock (keyBlock key) = keyBlock key := by
  rw [keyBlock, keyBlock_size]
  simp only [Nat.lt_irrefl, ↓reduceIte, keyBlock_size, Nat.sub_self, Array.replicate_zero]
  exact ByteArray.append_empty

theorem xorPad_keyBlock_size (key : ByteArray) (pad : UInt8) :
    (xorPad (keyBlock key) pad).size = 64 := by
  rw [xorPad_size, keyBlock_size]

theorem xorPad_zeroPad (key : ByteArray) (pad : UInt8) (fits : key.size ≤ 64) :
    xorPad (key ++ ⟨Array.replicate (64 - key.size) 0⟩) pad =
      ⟨(Array.range 64).map (fun i ↦ key.data[i]?.getD 0 ^^^ pad)⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [xorPad, ByteArray.data_append, Array.size_map, Array.size_append,
      Array.size_replicate, Array.size_range]
    change key.size + (64 - key.size) = 64
    omega
  · intro i left right
    simp only [xorPad, Array.getElem_map, ByteArray.data_append, Array.getElem_range]
    by_cases inside : i < key.size
    · rw [Array.getElem_append_left inside, Array.getElem?_eq_getElem inside]
      rfl
    · have outside : key.data.size ≤ i := by change key.size ≤ i; omega
      rw [Array.getElem_append_right outside, Array.getElem?_eq_none outside]
      simp only [Array.getElem_replicate, Option.getD_none]

theorem hmac_sha256_eq (key input : ByteArray) :
    Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input =
      SHA256.hashBytes (xorPad (keyBlock key) 0x5c ++
        SHA256.hashBytes (xorPad (keyBlock key) 0x36 ++ input)) := by
  unfold Standards.RFC.HMAC.hmac keyBlock
  split
  · rw [xorPad_zeroPad _ _ (by rw [sha256_hashBytes_size]; omega),
      xorPad_zeroPad _ _ (by rw [sha256_hashBytes_size]; omega)]
  · rename_i fits
    rw [xorPad_zeroPad _ _ (by omega), xorPad_zeroPad _ _ (by omega)]

theorem hmac_sha256_size (key input : ByteArray) :
    (Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input).size = 32 := by
  rw [hmac_sha256_eq, sha256_hashBytes_size]

theorem hmac_sha256_keyBlock (key input : ByteArray) :
    Standards.RFC.HMAC.hmac SHA256.hashBytes 64 (keyBlock key) input =
      Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input := by
  rw [hmac_sha256_eq, hmac_sha256_eq key input, keyBlock_idempotent]

theorem hmac_sha256_of_key_size_le (key input : ByteArray) (fits : key.size ≤ 64) :
    Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input =
      SHA256.hashBytes (xorPad (key ++ ⟨Array.replicate (64 - key.size) 0⟩) 0x5c ++
        SHA256.hashBytes (xorPad (key ++ ⟨Array.replicate (64 - key.size) 0⟩) 0x36 ++ input)) := by
  rw [hmac_sha256_eq]
  have not_large : ¬64 < key.size := by omega
  simp only [keyBlock, not_large, ↓reduceIte]

theorem hmac_sha256_of_key_size_gt (key input : ByteArray) (large : 64 < key.size) :
    Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input =
      SHA256.hashBytes (xorPad (SHA256.hashBytes key ++ ⟨Array.replicate 32 0⟩) 0x5c ++
        SHA256.hashBytes (xorPad (SHA256.hashBytes key ++ ⟨Array.replicate 32 0⟩) 0x36 ++ input)) := by
  rw [hmac_sha256_eq]
  simp only [keyBlock, large, ↓reduceIte, sha256_hashBytes_size]

theorem hmac_sha256_hash_key (key input : ByteArray) (large : 64 < key.size) :
    Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input =
      Standards.RFC.HMAC.hmac SHA256.hashBytes 64 (SHA256.hashBytes key) input := by
  rw [hmac_sha256_of_key_size_gt key input large,
    hmac_sha256_of_key_size_le _ input (by rw [sha256_hashBytes_size]; omega)]
  simp only [sha256_hashBytes_size]

end Hkdf.Proofs.Common.HMAC
