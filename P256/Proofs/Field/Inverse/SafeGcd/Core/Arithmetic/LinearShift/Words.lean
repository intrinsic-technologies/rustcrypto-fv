import P256.Proofs.Field.Schoolbook.Arithmetic
import X86Proofs.Instructions.Shrd.Operation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Words
open X86Proofs
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Field.Schoolbook

def shiftedWords (a : Vector (BitVec 64) 5) (s : Nat) : Vector (BitVec 64) 4 :=
  Vector.ofFn fun i ↦ a[i.val] >>> s ||| a[i.val + 1] <<< (64 - s)

private theorem word_value_for (n : Nat) (a b : BitVec n) (s : Nat) (hs : s ≤ n) :
    (a >>> s ||| b <<< (n-s)).toNat = ((b.toNat*2^n+a.toNat)/2^s)%2^n := by
  have hb : b.toNat*2^n+a.toNat < 2^(n+n) := by
    calc
      _ < b.toNat*2^n+2^n := Nat.add_lt_add_left a.isLt _
      _ = (b.toNat+1)*2^n := (Nat.succ_mul _ _).symm
      _ ≤ 2^n*2^n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt b.isLt)
      _ = 2^(n+n) := (Nat.pow_add _ _ _).symm
  have h := congrArg (fun x : BitVec n ↦ x.toNat)
    (shrdResult_eq_extract (m := n+n) rfl s hs a b)
  simpa only [shrdResult, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hb] using h.symm

theorem word_value (a b : BitVec 64) (s : Nat) (hs : s ≤ 64) :
    (a >>> s ||| b <<< (64-s)).toNat = ((b.toNat*2^64+a.toNat)/2^s)%2^64 :=
  word_value_for 64 a b s hs

set_option exponentiation.threshold 512 in
private theorem split_identity (D K a0 a1 a2 a3 a4 : Nat)
    (hk : D*K = 2^64) :
    a0 + 2^64*a1 + 2^128*a2 + 2^192*a3 + 2^256*a4 =
      D * ((a0/D+K*(a1%D)) + 2^64*(a1/D+K*(a2%D)) +
        2^128*(a2/D+K*(a3%D)) + 2^192*(a3/D+K*(a4%D)) + 2^256*(a4/D)) + a0%D := by
  have h0 := Nat.mod_add_div a0 D
  have h1 := Nat.mod_add_div a1 D
  have h2 := Nat.mod_add_div a2 D
  have h3 := Nat.mod_add_div a3 D
  have h4 := Nat.mod_add_div a4 D
  grind only

private theorem split_lt (D K a b : Nat) (hD : 0 < D)
    (hk : D*K = 2^64) (ha : a < 2^64) :
    a/D + K*(b%D) < 2^64 := by
  have hq : a/D < K := (Nat.div_lt_iff_lt_mul hD).mpr (by simpa [Nat.mul_comm, hk] using ha)
  have hr := Nat.mod_lt b hD
  have hb := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hr)
  have hb' : K*(b%D)+K ≤ 2^64 := by
    simpa only [Nat.mul_succ, Nat.mul_comm K D, hk] using hb
  omega

set_option exponentiation.threshold 512 in
private theorem word_split_nat (D K a b : Nat) (hD : 0 < D)
    (hk : D*K = 2^64) (ha : a < 2^64) :
    ((b*2^64+a)/D)%2^64 = a/D+K*(b%D) := by
  have h0 := Nat.mod_add_div a D
  have h1 := Nat.mod_add_div b D
  have he : b*2^64+a = D*(a/D+K*(b%D)+2^64*(b/D))+a%D := by
    grind only
  rw [he, Nat.mul_add_div hD, Nat.div_eq_of_lt (Nat.mod_lt a hD), Nat.add_zero,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (split_lt D K a b hD hk ha)]

theorem word_split (a b : BitVec 64) (s : Nat) (hs : s ≤ 64) :
    (a >>> s ||| b <<< (64-s)).toNat = a.toNat/2^s+2^(64-s)*(b.toNat%2^s) := by
  rw [word_value a b s hs]
  apply word_split_nat _ _ _ _ (Nat.two_pow_pos _) _ a.isLt
  rw [← Nat.pow_add, Nat.add_sub_of_le hs]

set_option exponentiation.threshold 512 in
private theorem full_nat (D K a0 a1 a2 a3 a4 : Nat) (hD : 0 < D)
    (hk : D*K = 2^64) (h0 : a0 < 2^64) (h1 : a1 < 2^64)
    (h2 : a2 < 2^64) (h3 : a3 < 2^64) :
    (a0/D+K*(a1%D)) + 2^64*(a1/D+K*(a2%D)) +
      2^128*(a2/D+K*(a3%D)) + 2^192*(a3/D+K*(a4%D)) =
    ((a0 + 2^64*a1 + 2^128*a2 + 2^192*a3 + 2^256*a4)/D)%2^256 := by
  have b0 := split_lt D K a0 a1 hD hk h0
  have b1 := split_lt D K a1 a2 hD hk h1
  have b2 := split_lt D K a2 a3 hD hk h2
  have b3 := split_lt D K a3 a4 hD hk h3
  conv => rhs; rw [split_identity D K a0 a1 a2 a3 a4 hk, Nat.mul_add_div hD,
    Nat.div_eq_of_lt (Nat.mod_lt a0 hD), Nat.add_zero, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem shiftedWords_value (a : Vector (BitVec 64) 5) (s : Nat) (hs : s ≤ 64) :
    packFour ((shiftedWords a s).map BitVec.toNat) =
      (packFive (a.map BitVec.toNat)/2^s)%2^256 := by
  have hk : 2^s*2^(64-s)=2^64 := by rw [← Nat.pow_add, Nat.add_sub_of_le hs]
  have h := full_nat (2^s) (2^(64-s)) a[0].toNat a[1].toNat a[2].toNat
    a[3].toNat a[4].toNat (Nat.two_pow_pos s) hk a[0].isLt a[1].isLt a[2].isLt a[3].isLt
  simpa only [packFour, packFive, Vector.getElem_map, shiftedWords, Vector.getElem_ofFn,
    wordBase, word_split _ _ s hs, Nat.reduceAdd, Nat.reducePow] using h

theorem shiftedWords_value_exact (a : Vector (BitVec 64) 5) (s : Nat) (hs : s ≤ 64)
    (h : packFive (a.map BitVec.toNat)/2^s < 2^256) :
    packFour ((shiftedWords a s).map BitVec.toNat) = packFive (a.map BitVec.toNat)/2^s := by
  rw [shiftedWords_value a s hs, Nat.mod_eq_of_lt h]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Words
