import Standards.RFC.MD5.Processing
import Standards.RFC.MD5.Conversion
import Init.Data.Range.Lemmas
import Init.Data.ByteArray.Lemmas

namespace Md5.Proofs.RFC1321

open Standards.RFC.MD5

theorem size_wordsOfBytes (bytes : ByteArray) : (wordsOfBytes bytes).size = bytes.size / 4 := by
  simp [wordsOfBytes]

theorem getElem_wordsOfBytes (bytes : ByteArray) (i : Nat)
    (hi : i < (wordsOfBytes bytes).size) :
    (wordsOfBytes bytes)[i] =
      (bytes.extract (4 * i) (4 * i + 4)).data.foldr
        (fun (byte : UInt8) (word : BitVec 32) ↦ (word <<< 8) ||| BitVec.ofNat 32 byte.toNat)
        (0 : BitVec 32) := by
  simp [wordsOfBytes]

theorem wordsOfBytes_append (a b : ByteArray) (ha : a.size % 4 = 0) :
    wordsOfBytes (a ++ b) = wordsOfBytes a ++ wordsOfBytes b := by
  apply Array.ext
  · simp only [size_wordsOfBytes, ByteArray.size_append, Array.size_append]
    omega
  · intro i hi hi'
    by_cases hia : i < (wordsOfBytes a).size
    · rw [Array.getElem_append_left hia, getElem_wordsOfBytes, getElem_wordsOfBytes]
      have hend : 4 * i + 4 ≤ a.size := by rw [size_wordsOfBytes] at hia; omega
      have hgroup : (a ++ b).extract (4 * i) (4 * i + 4) =
          a.extract (4 * i) (4 * i + 4) := by
        rw [ByteArray.extract_append]
        have hstart : 4 * i - a.size = 0 := by omega
        have hstop : 4 * i + 4 - a.size = 0 := by omega
        simp [hstart, hstop]
      rw [hgroup]
    · rw [Array.getElem_append_right (by omega), getElem_wordsOfBytes, getElem_wordsOfBytes]
      have hindex : 4 * i = a.size + 4 * (i - (wordsOfBytes a).size) := by
        rw [size_wordsOfBytes] at *
        omega
      rw [hindex, Nat.add_assoc, ByteArray.extract_append_size_add]

theorem wordsOfBytes_extract (bytes : ByteArray) (start stop : Nat) :
    wordsOfBytes (bytes.extract (4 * start) (4 * stop)) =
      (wordsOfBytes bytes).extract start stop := by
  apply Array.ext
  · simp only [size_wordsOfBytes, ByteArray.size_extract, Array.size_extract]
    omega
  · intro i hi hi'
    rw [getElem_wordsOfBytes, Array.getElem_extract, getElem_wordsOfBytes]
    have hibound : i < min stop (bytes.size / 4) - start := by
      simpa only [Array.size_extract, size_wordsOfBytes] using hi'
    have hgroup : (bytes.extract (4 * start) (4 * stop)).extract (4 * i) (4 * i + 4) =
        bytes.extract (4 * (start + i)) (4 * (start + i) + 4) := by
      rw [ByteArray.extract_extract]
      have hlo : 4 * start + 4 * i = 4 * (start + i) := by omega
      have hhi : min (4 * start + (4 * i + 4)) (4 * stop) =
          4 * (start + i) + 4 := by omega
      rw [hlo, hhi]
    rw [hgroup]

theorem processBlocks_eq_foldl (buffer : Buffer) (M : Array (BitVec 32)) :
    processBlocks buffer M = (List.range (M.size / 16)).foldl
      (fun state i ↦ processBlock state (Vector.ofFn fun j ↦ M.getD (i * 16 + j.val) 0))
      buffer := by
  unfold processBlocks
  simp [List.range_eq_range']

theorem processBlocks_empty (buffer : Buffer) : processBlocks buffer #[] = buffer := by
  simp [processBlocks_eq_foldl]

theorem processBlocks_of_size_lt (buffer : Buffer) (M : Array (BitVec 32))
    (hM : M.size < 16) : processBlocks buffer M = buffer := by
  rw [processBlocks_eq_foldl, Nat.div_eq_of_lt hM]
  rfl

theorem processBlocks_one (buffer : Buffer) (M : Array (BitVec 32))
    (hM : M.size / 16 = 1) :
    processBlocks buffer M = processBlock buffer (Vector.ofFn fun j ↦ M.getD j.val 0) := by
  rw [processBlocks_eq_foldl, hM]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
    List.foldl_nil, Nat.zero_mul, Nat.zero_add]

theorem processBlocks_append (buffer : Buffer) (a b : Array (BitVec 32))
    (ha : a.size % 16 = 0) :
    processBlocks buffer (a ++ b) = processBlocks (processBlocks buffer a) b := by
  have hsize : (a ++ b).size / 16 = a.size / 16 + b.size / 16 := by
    rw [Array.size_append]
    omega
  simp only [processBlocks_eq_foldl, hsize, List.range_add, List.foldl_append, List.foldl_map]
  have hleft : ∀ i ∈ List.range (a.size / 16), ∀ state,
      processBlock state (Vector.ofFn fun j ↦ (a ++ b).getD (i * 16 + j.val) 0) =
      processBlock state (Vector.ofFn fun j ↦ a.getD (i * 16 + j.val) 0) := by
    intro i hi state
    have hi' := List.mem_range.mp hi
    apply congrArg (processBlock state)
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    have hidx : i * 16 + j < a.size := by omega
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hidx]
  have hright : ∀ i state,
      processBlock state
        (Vector.ofFn fun j ↦ (a ++ b).getD ((a.size / 16 + i) * 16 + j.val) 0) =
      processBlock state (Vector.ofFn fun j ↦ b.getD (i * 16 + j.val) 0) := by
    intro i state
    apply congrArg (processBlock state)
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    have hoff : (a.size / 16 + i) * 16 + j = a.size + (i * 16 + j) := by omega
    rw [hoff]
    simp only [Array.getD_eq_getD_getElem?,
      Array.getElem?_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left]
  have hfold : (List.range (a.size / 16)).foldl
      (fun state i ↦ processBlock state
        (Vector.ofFn fun j ↦ (a ++ b).getD (i * 16 + j.val) 0)) buffer =
      (List.range (a.size / 16)).foldl
        (fun state i ↦ processBlock state (Vector.ofFn fun j ↦ a.getD (i * 16 + j.val) 0))
        buffer := by
    apply List.foldl_rel (r := Eq) (by rfl)
    intro i hi v w hv
    subst w
    exact hleft i hi v
  rw [hfold]
  apply List.foldl_rel (r := Eq) (by rfl)
  intro i _hi v w hv
  subst w
  exact hright i v

theorem processBlocks_cons (buffer : Buffer) (M : Array (BitVec 32))
    (hM : 16 ≤ M.size) :
    processBlocks buffer M =
      processBlocks (processBlock buffer (Vector.ofFn fun j ↦ M.getD j.val 0))
        (M.extract 16 M.size) := by
  have hsplit : M = M.extract 0 16 ++ M.extract 16 M.size := by
    simp [Array.extract_append_extract, hM]
  conv => lhs; rw [hsplit, processBlocks_append buffer _ _ (by simp; omega)]
  have hfirst : processBlocks buffer (M.extract 0 16) =
      processBlock buffer (Vector.ofFn fun j ↦ M.getD j.val 0) := by
    rw [processBlocks_one buffer _ (by simp; omega)]
    apply congrArg (processBlock buffer)
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have hiM : i < M.size := by omega
    have hiE : i < (M.extract 0 16).size := by simp; omega
    rw [← Array.getElem_eq_getD (h := hiM), ← Array.getElem_eq_getD (h := hiE)]
    simp
  rw [hfirst]

theorem processBlocks_wordsOfBytes_append (buffer : Buffer) (a b : ByteArray)
    (ha : a.size % 64 = 0) :
    processBlocks buffer (wordsOfBytes (a ++ b)) =
      processBlocks (processBlocks buffer (wordsOfBytes a)) (wordsOfBytes b) := by
  rw [wordsOfBytes_append a b (by omega)]
  apply processBlocks_append
  rw [size_wordsOfBytes]
  omega

end Md5.Proofs.RFC1321
