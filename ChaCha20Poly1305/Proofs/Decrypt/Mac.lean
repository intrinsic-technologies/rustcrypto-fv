import ChaCha20Poly1305.Proofs.Decrypt.PolyBounds
import Standards.RFC.ChaCha20Poly1305.AEAD
import Init.Data.Range.Lemmas
import Init.Data.ByteArray.Lemmas

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305
open Standards.RFC.ChaCha20Poly1305

private theorem foldLE (bs : List UInt8) (n : Nat) :
    bs.foldr (fun b k => b.toNat + 256*k) n =
      bs.foldr (fun b k => b.toNat + 256*k) 0 + 256^bs.length*n := by
  induction bs with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    rw [ih]
    grind

theorem le_append (a b : ByteArray) : leBytesToNum (a++b) = leBytesToNum a + 256^a.size*leBytesToNum b := by
  unfold leBytesToNum
  simp only [ByteArray.data_append, Array.foldr_append]
  rw [← Array.foldr_toList, foldLE]
  simp

theorem le_bound (a : ByteArray) : leBytesToNum a < 256^a.size := by
  obtain ⟨⟨as⟩⟩ := a
  change as.toArray.foldr _ 0 < 256^as.toArray.size
  rw [← Array.foldr_toList]
  simp only [List.size_toArray]
  induction as with
  | nil => decide
  | cons a as ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have := a.toNat_lt
    omega

def rKey (k : Vector UInt8 32) := clamp (leBytesToNum ⟨k.toArray.extract 0 16⟩)
def padKey (k : Vector UInt8 32) := leBytesToNum ⟨k.toArray.extract 16 32⟩

def blockNumber (msg : ByteArray) (i : Nat) :=
  leBytesToNum (msg.extract (16*i) (16*(i+1)))
def foldBlocks (msg : ByteArray) (r : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => (r*(foldBlocks msg r i + (blockNumber msg i + 2^128))) % modulus

private theorem fold_full {msg : ByteArray} {blocks : Nat} (hm : msg.size = blocks*16)
    (r : Nat) (i : Nat) (hi : i ≤ blocks) :
    (List.range' 1 i).foldl (fun a j =>
      (r*(a + leBytesToNum (msg.extract ((j - 1)*16) (min (j*16-1) (msg.size-1)+1) ++ ⟨#[0x01]⟩))) % modulus) 0 =
      foldBlocks msg r i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    have hEnd : min ((1+i)*16 - 1) (msg.size-1) + 1 = 16*(i+1) := by omega
    have hStart : (1+i-1)*16 = 16*i := by omega
    rw [hEnd,hStart, le_append]
    have hLen : (msg.extract (16*i) (16*(i+1))).size = 16 := by rw [ByteArray.size_extract]; omega
    rw [hLen]
    rfl

theorem mac_full {msg : ByteArray} {blocks : Nat} (hm : msg.size = blocks*16)
    (key : Vector UInt8 32) :
    poly1305Mac msg key = numTo16LeBytes (foldBlocks msg (rKey key) blocks + padKey key) := by
  unfold poly1305Mac
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
  have hlen : (msg.size + 15)/16 = blocks := by omega
  rw [hlen]
  simp only [Nat.add_one_sub_one, Nat.div_one]
  exact congrArg (fun a => numTo16LeBytes (a + padKey key)) (fold_full hm (rKey key) blocks (Nat.le_refl _))

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
