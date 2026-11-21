import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Encoding

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression

open Hkdf.Proofs.NIST

theorem bitsToNat_testBit (bits : Array Bool) (i : Nat) (hi : i < bits.size) :
    (Encoding.bitsToNat bits).testBit i = bits[bits.size - 1 - i]! := by
  rcases bits with ⟨items⟩
  generalize hr : items.reverse = rev
  have he : items = rev.reverse := by rw [← hr, List.reverse_reverse]
  subst items
  clear hr
  induction rev generalizing i with
  | nil => simp_all
  | cons bit rev ih =>
    let bits := rev.reverse.toArray
    simp only [List.reverse_cons] at hi ⊢
    have hpush : (⟨rev.reverse ++ [bit]⟩ : Array Bool) = bits.push bit := by
      apply Array.toList_inj.mp
      simp [bits]
    rw [hpush] at hi ⊢
    change ∀ (i : Nat), i < bits.size → _ at ih
    have hfold : Encoding.bitsToNat (bits.push bit) =
        2 * Encoding.bitsToNat bits + if bit then 1 else 0 := by
      simp only [Encoding.bitsToNat, Array.foldl_push]
    rw [hfold]
    cases i with
    | zero =>
      cases bit <;> simp [Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * Encoding.bitsToNat bits + (if bit then 1 else 0)) / 2 =
          Encoding.bitsToNat bits := by cases bit <;> simp <;> omega
      rw [hdiv, ih i (by simp only [Array.size_push] at hi; omega)]
      have hind : (bits.push bit).size - 1 - (i + 1) = bits.size - 1 - i := by
        simp only [Array.size_push] at hi ⊢
        omega
      have hj : bits.size - 1 - i < bits.size := by
        simp only [Array.size_push] at hi
        omega
      rw [hind, getElem!_pos bits _ hj,
        getElem!_pos (bits.push bit) _ (by simpa only [Array.size_push] using Nat.lt_succ_of_lt hj),
        Array.getElem_push_lt hj]

end Hkdf.Proofs.Common.SHA256.Compression
