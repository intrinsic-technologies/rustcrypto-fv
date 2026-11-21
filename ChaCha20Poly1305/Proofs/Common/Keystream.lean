import ChaCha20Poly1305.Spec.AEAD

namespace ChaCha20Poly1305.Proofs.Common

private def xorBytes (block : ByteArray) (keyStream : Vector UInt8 64) : ByteArray :=
  ⟨Array.ofFn fun i : Fin block.size => block[i] ^^^ keyStream[i.val]!⟩

private def xorBlock (ks : Nat → Vector UInt8 64) (message : ByteArray) (j : Nat) : ByteArray :=
  xorBytes (message.extract (j * 64) (j * 64 + 64)) (ks j)

def xorKeystream (ks : Nat → Vector UInt8 64) (message : ByteArray) : ByteArray := Id.run do
  let mut encryptedMessage := ByteArray.empty
  for j in [0:message.size / 64] do
    let block := message.extract (j * 64) (j * 64 + 64)
    encryptedMessage := encryptedMessage ++ xorBytes block (ks j)
  if message.size % 64 ≠ 0 then
    let j := message.size / 64
    let block := message.extract (j * 64) message.size
    encryptedMessage := encryptedMessage ++ xorBytes block (ks j)
  return encryptedMessage

private theorem vec_getElem_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (h : i < n)
    (d : α) : v[i]'h = v.getD i d := by
  have hv : i < v.toArray.size := by simpa using h
  change v.toArray[i]'hv = _
  exact Array.getElem_eq_getD d

private theorem vec_getElem_bang_getD {α : Type} [Inhabited α] {n : Nat} (v : Vector α n)
    (i : Nat) : v[i]! = v.getD i default := by
  by_cases h : i < n
  · rw [getElem!_pos v i h]
    exact vec_getElem_getD v i h _
  · simp [Vector.getD, Array.getD, h]

private theorem xorBytes_size (block : ByteArray) (stream : Vector UInt8 64) :
    (xorBytes block stream).size = block.size := by
  unfold xorBytes
  change (Array.ofFn _).size = _
  rw [Array.size_ofFn]

private theorem xorBytes_getElem (block : ByteArray) (stream : Vector UInt8 64) (i : Nat)
    (hi : i < (xorBytes block stream).size) :
    (xorBytes block stream)[i] = block[i]'(by rw [xorBytes_size] at hi; exact hi) ^^^ stream.getD i 0 := by
  have hb : i < block.size := by
    change i < (Array.ofFn _).size at hi
    rw [Array.size_ofFn] at hi
    exact hi
  unfold xorBytes
  change (Array.ofFn _)[i]'(by simpa using hb) = _
  rw [Array.getElem_ofFn (by simpa using hb)]
  rw [vec_getElem_bang_getD]
  rfl

private theorem xorBlock_size (ks : Nat → Vector UInt8 64) (message : ByteArray) (j : Nat) :
    (xorBlock ks message j).size = min 64 (message.size - 64 * j) := by
  unfold xorBlock
  rw [xorBytes_size, ByteArray.size_extract]
  omega

private theorem xorBlock_getElem (ks : Nat → Vector UInt8 64) (message : ByteArray) (j i : Nat)
    (hi : i < (xorBlock ks message j).size) :
    (xorBlock ks message j)[i] = message[j * 64 + i]'(by
      have hs := xorBlock_size ks message j
      rw [hs] at hi
      omega) ^^^ (ks j).getD i 0 := by
  have hi' := hi
  rw [xorBlock_size] at hi'
  have hb : i < (message.extract (64 * j) (64 * j + 64)).size := by
    rw [ByteArray.size_extract]
    omega
  unfold xorBlock
  have hb' : i < (message.extract (j * 64) (j * 64 + 64)).size := by
    simpa only [Nat.mul_comm] using hb
  have hx := xorBytes_getElem (message.extract (j * 64) (j * 64 + 64)) (ks j) i (by
    rw [xorBytes_size]
    exact hb')
  rw [ByteArray.getElem_extract hb'] at hx
  exact hx

private theorem xorBlock_getElem_index (ks : Nat → Vector UInt8 64) (message : ByteArray)
    (j i : Nat) (hi : i < (xorBlock ks message j).size) :
    (xorBlock ks message j)[i] = message[j * 64 + i]'(by
      have hs := xorBlock_size ks message j
      rw [hs] at hi
      omega) ^^^ (ks j)[i]'(by
      have hs := xorBlock_size ks message j
      rw [hs] at hi
      omega) := by
  rw [xorBlock_getElem ks message j i hi]
  have h64 : i < 64 := by rw [xorBlock_size] at hi; omega
  have hmsg : j * 64 + i < message.size := by
    rw [xorBlock_size] at hi
    omega
  exact congrArg (fun x => message[j * 64 + i]'hmsg ^^^ x)
    ((vec_getElem_getD (ks j) i h64 0).symm)

private def xorPrefix (ks : Nat → Vector UInt8 64) (message : ByteArray) (count : Nat) : ByteArray :=
  (List.range count).foldl (fun out j => out ++ xorBlock ks message j) ByteArray.empty

theorem xorPrefix_succ (ks : Nat → Vector UInt8 64) (message : ByteArray) (count : Nat) :
    xorPrefix ks message (count + 1) = xorPrefix ks message count ++ xorBlock ks message count := by
  unfold xorPrefix
  rw [List.range_succ]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem xorPrefix_size (ks : Nat → Vector UInt8 64) (message : ByteArray) (count : Nat) :
    (xorPrefix ks message count).size = min (64 * count) message.size := by
  induction count with
  | zero => simp [xorPrefix]
  | succ n ih =>
      rw [xorPrefix_succ, ByteArray.size_append, xorBlock_size, ih]
      omega

private theorem xorPrefix_getElem (ks : Nat → Vector UInt8 64) (message : ByteArray) (count i : Nat)
    (hi : i < (xorPrefix ks message count).size) :
    (xorPrefix ks message count)[i] = message[i]'(by
      have hs := xorPrefix_size ks message count
      rw [hs] at hi
      omega) ^^^ (ks (i / 64))[i % 64]'(by
      have hs := xorPrefix_size ks message count
      rw [hs] at hi
      omega) := by
  induction count with
  | zero => simp [xorPrefix] at hi
  | succ count ih =>
      by_cases hl : i < (xorPrefix ks message count).size
      · simp only [xorPrefix_succ, ByteArray.getElem_append_left hl]
        exact ih hl
      · have hn : (xorPrefix ks message count).size = 64 * count := by
          rw [xorPrefix_size] at hi hl ⊢
          omega
        simp only [xorPrefix_succ, ByteArray.getElem_append_right (Nat.le_of_not_gt hl), hn]
        have he : i / 64 = count := by rw [xorPrefix_size] at hi; omega
        have hm : i % 64 = i - 64 * count := by omega
        have hi' := hi
        rw [xorPrefix_succ, ByteArray.size_append, xorBlock_size, hn] at hi'
        have hp := xorBlock_getElem_index ks message count (i - 64 * count) (by
          rw [xorBlock_size]
          omega)
        have hadd : count * 64 + (i - 64 * count) = i := by omega
        simpa only [hadd, he, hm] using hp

private theorem xorKeystream_eq_prefix (ks : Nat → Vector UInt8 64) (message : ByteArray) :
    xorKeystream ks message = xorPrefix ks message ((message.size + 63) / 64) := by
  unfold xorKeystream xorPrefix
  dsimp
  split <;> rename_i hmod
  all_goals simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  all_goals rw [List.range'_eq_map_range]
  · have hm := Nat.mod_add_div message.size 64
    have hceil : (message.size + 63) / 64 = message.size / 64 + 1 := by omega
    rw [hceil, List.range_succ]
    have htail : message.extract (64 * (message.size / 64)) message.size =
        message.extract (64 * (message.size / 64)) (64 * (message.size / 64) + 64) := by
      apply ByteArray.ext
      rw [ByteArray.data_extract, ByteArray.data_extract]
      apply Array.ext
      · simp only [Array.size_extract, ByteArray.size_data]
        omega
      · intro i hi1 hi2
        rw [Array.getElem_extract hi1, Array.getElem_extract hi2]
    simp [xorBlock, htail, List.foldl_append, Nat.mul_comm]
  · have hceil : (message.size + 63) / 64 = message.size / 64 := by omega
    rw [hceil]
    simp [xorBlock]

theorem xorKeystream_size (ks : Nat → Vector UInt8 64) (message : ByteArray) :
    (xorKeystream ks message).size = message.size := by
  rw [xorKeystream_eq_prefix, xorPrefix_size]
  omega

theorem xorKeystream_getElem (ks : Nat → Vector UInt8 64) (message : ByteArray) (i : Nat)
    (hi : i < message.size) :
    (xorKeystream ks message)[i]'(by
      have hs := xorKeystream_size ks message
      omega) = message[i] ^^^ (ks (i / 64))[i % 64]'(by
        have : i % 64 < 64 := Nat.mod_lt _ (by decide)
        simpa using this) := by
  have hp := xorPrefix_getElem ks message ((message.size + 63) / 64) i (by
    rw [xorPrefix_size]
    omega)
  simpa only [xorKeystream_eq_prefix] using hp

theorem xorKeystream_involutive (ks : Nat → Vector UInt8 64) (message : ByteArray) :
    xorKeystream ks (xorKeystream ks message) = message := by
  apply ByteArray.ext_getElem
  · rw [xorKeystream_size, xorKeystream_size]
  · intro i hi hj
    rw [xorKeystream_getElem ks _ i (by rw [xorKeystream_size] at hi; omega),
      xorKeystream_getElem ks message i hj]
    simp only [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

end ChaCha20Poly1305.Proofs.Common
