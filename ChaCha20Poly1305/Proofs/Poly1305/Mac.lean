import Standards.RFC.ChaCha20Poly1305.AEAD
import Standards.RFC.ChaCha20Poly1305.Poly1305
import ChaCha20Poly1305.Proofs.Common.Poly1305State

namespace ChaCha20Poly1305.Proofs.Poly1305.Mac

open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.Poly1305State

def absorbBlock (r a : Nat) (block : ByteArray) : Nat :=
  (r * (a + leBytesToNum (block ++ ⟨#[0x01]⟩))) % (2 ^ 130 - 5)

def absorbBlocks (r a : Nat) (bytes : ByteArray) : Nat :=
  (List.range (bytes.size / 16)).foldl
    (fun acc i => absorbBlock r acc (bytes.extract (16 * i) (16 * i + 16))) a

def lengthBlock (aad ciphertext : ByteArray) : ByteArray :=
  numTo8LeBytes aad.size ++ numTo8LeBytes ciphertext.size

set_option maxHeartbeats 1000000 in
theorem absorbBlocks_append (r a : Nat) (x y : ByteArray) (hx : x.size % 16 = 0) :
    absorbBlocks r a (x ++ y) = absorbBlocks r (absorbBlocks r a x) y := by
  unfold absorbBlocks
  let qx := x.size / 16
  let qy := y.size / 16
  have hq : (x ++ y).size / 16 = qx + qy := by
    dsimp [qx, qy]
    rw [ByteArray.size_append]
    omega
  have hleft : ∀ (j : Nat) (b : Nat), j ≤ qx →
      (List.range j).foldl (fun z i => absorbBlock r z ((x ++ y).extract (16*i) (16*i+16))) b =
      (List.range j).foldl (fun z i => absorbBlock r z (x.extract (16*i) (16*i+16))) b := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro b hj
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih _ (by omega)]
      congr 1
      apply ByteArray.ext
      rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
      simp only [ByteArray.size_data]
      have hh : 16 * j + 16 ≤ x.size := by dsimp [qx] at hj; omega
      simp [Nat.sub_eq_zero_of_le hh, hh]
  have hmap : ∀ (j : Nat) (b : Nat), j ≤ qy →
      (List.map (fun i => qx + i) (List.range j)).foldl
        (fun z i => absorbBlock r z ((x ++ y).extract (16*i) (16*i+16))) b =
      (List.range j).foldl (fun z i => absorbBlock r z (y.extract (16*i) (16*i+16))) b := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro b hj
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_singleton, List.foldl_cons, List.foldl_nil]
      rw [ih _ (by omega)]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      congr 1
      apply ByteArray.ext
      rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
      simp only [ByteArray.size_data]
      have hxs : x.size = 16 * qx := by dsimp [qx]; omega
      have hxd : x.data.size = 16 * qx := by simpa [ByteArray.size_data] using hxs
      rw [hxs]
      rw [Array.extract_eq_empty_of_le (by omega)]
      simp only [Array.empty_append]
      congr 1 <;> omega
  rw [hq, List.range_add, List.foldl_append]
  rw [hleft qx a (by omega), hmap qy _ (by omega)]

theorem absorbBlocks_single (r a : Nat) (block : ByteArray) (h : block.size = 16) :
    absorbBlocks r a block = absorbBlock r a block := by
  simp only [absorbBlocks, h, Nat.reduceDiv, List.range_one, List.foldl_cons, List.foldl_nil]
  congr 1
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by simpa [h] using h)

set_option maxHeartbeats 20000000 in
theorem poly1305Mac_aligned (msg : ByteArray) (key : Vector UInt8 32) (h : msg.size % 16 = 0) :
    poly1305Mac msg key = numTo16LeBytes (absorbBlocks (clampedR key) 0 msg + padOf key) := by
  unfold poly1305Mac
  simp only [Id.run]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [List.range'_eq_map_range]
  simp
  have hq : (msg.size + 15) / 16 = msg.size / 16 := by omega
  rw [hq]
  rw [List.foldl_map]
  change numTo16LeBytes _ = numTo16LeBytes _
  unfold absorbBlocks
  simp only [clampedR, padOf]
  congr 2
  have hf : ∀ (j : Nat) (b : Nat), j ≤ msg.size / 16 →
      (List.range j).foldl
        (fun x y =>
          clamp (leBytesToNum { data := key.toArray.extract 0 16 }) *
              (x + leBytesToNum (msg.extract ((1+y-1)*16) (min ((1+y)*16-1) (msg.size-1)+1) ++ ⟨#[1]⟩)) % (2^130-5)) b =
      (List.range j).foldl (fun acc i => absorbBlock (clampedR key) acc (msg.extract (16*i) (16*i+16))) b := by
    intro j
    induction j with
    | zero => intro b hb; simp
    | succ j ih =>
      intro b hb
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih _ (by omega)]
      congr 1
      unfold absorbBlock
      congr 2
      have hj : 16 * (j+1) ≤ msg.size := by
        have hm := Nat.mod_add_div msg.size 16
        omega
      have hdiv : msg.size = 16 * (msg.size / 16) := by
        have hm := Nat.mod_add_div msg.size 16
        omega
      have hq' : (msg.size + 15) / 16 = msg.size / 16 := by omega
      rw [Nat.min_eq_left (by omega), show (1 + j - 1) * 16 = 16 * j by omega,
        show (1 + j) * 16 - 1 + 1 = 16 * j + 16 by omega]
  exact hf (msg.size / 16) 0 (by omega)

set_option maxHeartbeats 20000000 in
theorem poly1305Mac_aeadMacData (aad ciphertext : ByteArray) (otk : Vector UInt8 32) :
    poly1305Mac (aeadMacData aad ciphertext) otk =
      numTo16LeBytes (absorbBlocks (clampedR otk)
        (absorbBlocks (clampedR otk) (absorbBlocks (clampedR otk) 0 (aad ++ pad16 aad))
          (ciphertext ++ pad16 ciphertext))
        (lengthBlock aad ciphertext) + padOf otk) := by
  have hpad : ∀ x : ByteArray, (x ++ pad16 x).size % 16 = 0 := by
    intro x
    by_cases hx : x.size % 16 = 0
    · simp [pad16, hx]
    · rw [ByteArray.size_append]
      have hp : (pad16 x).size = 16 - x.size % 16 := by
        simp only [pad16, hx, ↓reduceIte]; exact Array.size_replicate
      rw [hp]
      have hm := Nat.mod_add_div x.size 16
      omega
  have hlen : (lengthBlock aad ciphertext).size % 16 = 0 := by
    change (8 + 8) % 16 = 0
    decide
  have hdata : (aeadMacData aad ciphertext).size % 16 = 0 := by
    rw [show aeadMacData aad ciphertext =
      (aad ++ pad16 aad) ++ (ciphertext ++ pad16 ciphertext) ++ lengthBlock aad ciphertext by
        simp [aeadMacData, lengthBlock, ByteArray.append_assoc]]
    rw [ByteArray.size_append, ByteArray.size_append]
    have ha := hpad aad
    have hc := hpad ciphertext
    have hl := hlen
    omega
  rw [poly1305Mac_aligned _ _ hdata]
  congr 2
  rw [show aeadMacData aad ciphertext =
      (aad ++ pad16 aad) ++ (ciphertext ++ pad16 ciphertext) ++ lengthBlock aad ciphertext by
        simp [aeadMacData, lengthBlock, ByteArray.append_assoc]]
  have hac : (aad ++ pad16 aad ++ (ciphertext ++ pad16 ciphertext)).size % 16 = 0 := by
    rw [ByteArray.size_append]
    have ha := hpad aad
    have hc := hpad ciphertext
    omega
  rw [absorbBlocks_append (clampedR otk) 0 _ _ hac,
    absorbBlocks_append (clampedR otk) 0 (aad ++ pad16 aad) _ (hpad aad)]

set_option maxHeartbeats 1000000 in
theorem absorbBlocks_pad16 (r a : Nat) (bytes : ByteArray) :
    absorbBlocks r a (bytes ++ pad16 bytes) =
      if bytes.size % 16 = 0 then absorbBlocks r a bytes
      else absorbBlock r (absorbBlocks r a (bytes.extract 0 (bytes.size / 16 * 16)))
        (bytes.extract (bytes.size / 16 * 16) bytes.size ++
          ⟨Array.replicate (16 - bytes.size % 16) 0⟩) := by
  by_cases h : bytes.size % 16 = 0
  · simp [pad16, h, absorbBlocks]
  · simp only [pad16, h, ↓reduceIte]
    let m := bytes.size / 16 * 16
    let tail : ByteArray := bytes.extract m bytes.size ++
      ⟨Array.replicate (16 - bytes.size % 16) 0⟩
    have hm : m ≤ bytes.size := by dsimp [m]; omega
    have hsplit : bytes ++ pad16 bytes = bytes.extract 0 m ++ tail := by
      simp only [pad16, h, ↓reduceIte]
      apply ByteArray.ext
      dsimp [tail]
      change (bytes ++ ⟨Array.replicate (16 - bytes.size % 16) 0⟩ : ByteArray).data =
        (bytes.extract 0 m ++ tail).data
      simp only [tail, m, ByteArray.data_append, ByteArray.data_extract]
      have hjoin : bytes.data.extract 0 (bytes.size / 16 * 16) ++
          bytes.data.extract (bytes.size / 16 * 16) bytes.size = bytes.data := by
        rw [Array.extract_append_extract]
        simp only [Nat.zero_min]
        rw [Nat.max_eq_right (by omega)]
        exact Array.extract_eq_self_of_le (Nat.le_refl _)
      rw [← Array.append_assoc, hjoin]
    have htail : tail.size = 16 := by
      dsimp [tail, m]
      simp only [ByteArray.size_append, ByteArray.size_extract]
      change min bytes.size bytes.size - bytes.size / 16 * 16 +
        (Array.replicate (16 - bytes.size % 16) 0).size = 16
      simp only [Array.size_replicate]
      omega
    have hprefix : (bytes.extract 0 m).size % 16 = 0 := by
      rw [ByteArray.size_extract, Nat.min_eq_left hm]
      dsimp [m]
      omega
    have hsplit' : bytes ++ (⟨Array.replicate (16 - bytes.size % 16) 0⟩ : ByteArray) =
        bytes.extract 0 m ++ tail := by
      simpa only [pad16, h, ↓reduceIte] using hsplit
    rw [hsplit', absorbBlocks_append r a (bytes.extract 0 m) tail hprefix]
    have hs := absorbBlocks_single r (absorbBlocks r a (bytes.extract 0 m)) tail htail
    rw [hs]

set_option maxHeartbeats 1000000 in
theorem absorbBlocks_succ (r a : Nat) (bytes : ByteArray) (k : Nat)
    (hk : 16 * (k + 1) ≤ bytes.size) :
    absorbBlocks r a (bytes.extract 0 (16 * (k + 1))) =
      absorbBlock r (absorbBlocks r a (bytes.extract 0 (16 * k)))
        (bytes.extract (16 * k) (16 * k + 16)) := by
  unfold absorbBlocks
  have hq : (16 * (k + 1)) / 16 = k + 1 := by omega
  have hs1 : (bytes.extract 0 (16 * (k + 1))).size / 16 = k + 1 := by
    simp [ByteArray.size_extract, hk, hq]
  have hs0 : (bytes.extract 0 (16 * k)).size / 16 = k := by
    rw [ByteArray.size_extract]
    have hm : min (16 * k) bytes.size = 16 * k := by
      apply Nat.min_eq_left
      omega
    rw [hm]
    omega
  have hprefix : ∀ (j : Nat) (b : Nat), j ≤ k →
      (List.range j).foldl
          (fun acc i => absorbBlock r acc ((bytes.extract 0 (16 * (k + 1))).extract (16 * i) (16 * i + 16))) b =
      (List.range j).foldl
          (fun acc i => absorbBlock r acc ((bytes.extract 0 (16 * k)).extract (16 * i) (16 * i + 16))) b := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro b hj
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih _ (by omega)]
      congr 1
      apply ByteArray.ext
      simp only [ByteArray.data_extract, Array.extract_extract]
      simp only [Nat.zero_add]
      have h₁ : 16 * j + 16 ≤ 16 * (k + 1) := by omega
      have h₂ : 16 * j + 16 ≤ 16 * k := by omega
      rw [Nat.min_eq_left h₁, Nat.min_eq_left h₂]
  rw [hs1, hs0, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hprefix k a (by omega)]
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Array.extract_extract]
  simp only [Nat.zero_add]
  rw [Nat.min_eq_left (by omega)]


theorem absorbBlock_eq (r a : Nat) (block : ByteArray) :
    absorbBlock r a block = ((a + leBytesToNum (block ++ ⟨#[0x01]⟩)) * r) % prime := by
  unfold absorbBlock prime
  rw [Nat.mul_comm]

theorem absorbBlock_mod (r a : Nat) (block : ByteArray) :
    absorbBlock r (a % prime) block = absorbBlock r a block := by
  rw [absorbBlock_eq, absorbBlock_eq, Nat.mul_mod, Nat.add_mod, Nat.mod_mod,
    ← Nat.add_mod, ← Nat.mul_mod]

theorem absorbBlocks_lt (r a : Nat) (bytes : ByteArray) (ha : a < prime) :
    absorbBlocks r a bytes < prime := by
  unfold absorbBlocks
  generalize List.range (bytes.size / 16) = l
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [absorbBlock_eq]
    exact Nat.mod_lt _ (by decide)

end ChaCha20Poly1305.Proofs.Poly1305.Mac
