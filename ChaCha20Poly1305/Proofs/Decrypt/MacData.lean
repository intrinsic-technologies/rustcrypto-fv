import ChaCha20Poly1305.Proofs.Decrypt.Mac

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305
open Standards.RFC.ChaCha20Poly1305

def count (s : ByteArray) := (s.size+15)/16

def padded (s : ByteArray) := s ++ pad16 s

theorem paddedSize (s : ByteArray) : (padded s).size = 16*count s := by
  rw [padded,ByteArray.size_append]
  unfold pad16 count
  split
  · rw [ByteArray.size_empty]; omega
  · change s.size + (Array.replicate _ (0 : UInt8)).size = _
    rw [Array.size_replicate]; omega

private theorem le_zeroes (n : Nat) : leBytesToNum ⟨Array.replicate n 0⟩ = 0 := by
  unfold leBytesToNum
  rw [← Array.foldr_toList,Array.toList_replicate]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem block_padded (s : ByteArray) (i : Nat) : blockNumber (padded s) i = blockNumber s i := by
  simp only [blockNumber,padded,ByteArray.extract_append,le_append]
  suffices h : leBytesToNum ((pad16 s).extract (16*i-s.size) (16*(i+1)-s.size)) = 0 by rw [h,Nat.mul_zero,Nat.add_zero]
  unfold pad16
  split
  · have he (a b : Nat) : ByteArray.empty.extract a b = ByteArray.empty := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]; apply Array.extract_eq_empty_of_le
      simp
    rw [he]; rfl
  · have he (n a b : Nat) : (ByteArray.mk (Array.replicate n 0)).extract a b =
        ⟨Array.replicate (min b n-a) 0⟩ := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]; exact Array.extract_replicate
    rw [he,le_zeroes]

def stepAcc (r acc block : Nat) := r * (acc + (block + 2^128)) % modulus
def foldFrom (s : ByteArray) (r init : Nat) : Nat → Nat
  | 0 => init
  | i+1 => stepAcc r (foldFrom s r init i) (blockNumber s i)

theorem foldFrom_zero (s : ByteArray) (r n : Nat) : foldFrom s r 0 n = foldBlocks s r n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [foldFrom,foldBlocks,stepAcc,ih]

theorem fold_padded (s : ByteArray) (r a n : Nat) :
    foldFrom (padded s) r a n = foldFrom s r a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldFrom,foldFrom,ih,block_padded]

private theorem front {xs ys : ByteArray} {i : Nat} (hi : 16*(i+1) ≤ xs.size) :
    blockNumber (xs++ys) i = blockNumber xs i := by
  simp only [blockNumber,ByteArray.extract_append, Nat.sub_eq_zero_of_le hi,
    show 16*i-xs.size=0 by omega, ByteArray.extract_same, ByteArray.append_empty]

private theorem back {xs ys : ByteArray} {k : Nat} (hk : xs.size = 16*k) (i : Nat) :
    blockNumber (xs++ys) (k+i) = blockNumber ys i := by
  unfold blockNumber
  rw [ByteArray.extract_append]
  have e : xs.extract (16*(k+i)) (16*(k+i+1)) = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]; apply Array.extract_eq_empty_of_le
    rw [ByteArray.size_data]; omega
  rw [e,ByteArray.empty_append,show 16*(k+i)-xs.size=16*i by omega,
      show 16*(k+i+1)-xs.size=16*(i+1) by omega]

theorem fold_join {xs ys : ByteArray} {k : Nat} (hk : xs.size = 16*k) (r a n : Nat) :
    foldFrom (xs++ys) r a (k+n) = foldFrom ys r (foldFrom xs r a k) n := by
  have initial (j : Nat) (hj : j ≤ k) : foldFrom (xs++ys) r a j = foldFrom xs r a j := by
    induction j with
    | zero => rfl
    | succ j ih => rw [foldFrom,foldFrom,ih (by omega),front (by omega)]
  induction n with
  | zero => exact initial _ (Nat.le_refl _)
  | succ n ih => rw [show k+(n+1)=k+n+1 by omega,foldFrom,foldFrom,ih,back hk]

private theorem lengths_size (x : Nat) : (numTo8LeBytes x).size = 8 := Array.size_ofFn

theorem aeadData (a c : ByteArray) : aeadMacData a c =
    padded a ++ (padded c ++ (numTo8LeBytes a.size ++ numTo8LeBytes c.size)) := by
  simp only [aeadMacData,padded,ByteArray.append_assoc]

def lengthBlock (a c : Nat) := leBytesToNum (numTo8LeBytes a ++ numTo8LeBytes c)

theorem mac_parts (a c : ByteArray) (key : Vector UInt8 32) :
    poly1305Mac (aeadMacData a c) key = numTo16LeBytes
      (stepAcc (rKey key) (foldFrom c (rKey key) (foldFrom a (rKey key) 0 (count a)) (count c))
        (lengthBlock a.size c.size) + padKey key) := by
  have la := paddedSize a; have lc := paddedSize c
  have hlen : (numTo8LeBytes a.size ++ numTo8LeBytes c.size).size = 16 := by
    rw [ByteArray.size_append,lengths_size,lengths_size]
  rw [aeadData,mac_full (blocks := count a+(count c+1)) (by
    simp only [ByteArray.size_append,la,lc,lengths_size]; omega), ← foldFrom_zero,fold_join la,
    fold_join lc,fold_padded,fold_padded,foldFrom]
  simp only [foldFrom,blockNumber, Nat.mul_zero]
  change numTo16LeBytes (stepAcc _ _ (leBytesToNum ((numTo8LeBytes a.size ++ numTo8LeBytes c.size).extract 0 16)) + _) = _
  have whole := ByteArray.extract_zero_size (b := numTo8LeBytes a.size ++ numTo8LeBytes c.size)
  rw [hlen] at whole
  rw [whole]
  rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
