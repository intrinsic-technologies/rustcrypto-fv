import Hkdf.Proofs.Common.SHA256.Compression.Values.Program
import Hkdf.Proofs.Common.SHA256.Compression.Values.Registers
import Hkdf.Proofs.Common.SHA256.Compression.InputWords

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

theorem low_extend (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  exact (BitVec.setWidth_setWidth_of_le x (by decide : 32 ≤ 64)).trans (BitVec.setWidth_eq x)

theorem low_add (x y : BitVec 64) : (x + y).setWidth 32 = x.setWidth 32 + y.setWidth 32 :=
  BitVec.setWidth_add x y (by decide)

theorem low_append (x y : BitVec 32) : (x ++ y).setWidth 32 = y :=
  BitVec.setWidth_append_eq_right

theorem choice_xor (x y z : BitVec 32) :
    ((y ^^^ z) &&& x) ^^^ z = (x &&& y) + (~~~x &&& z) := by
  rw [← bitVecChoice_eq_and_xor, ← bitVecChoice_eq_add_and]

theorem choice_xor_commuted (x y z : BitVec 32) :
    ((z ^^^ y) &&& x) ^^^ z = (x &&& y) + (~~~x &&& z) := by
  calc
    ((z ^^^ y) &&& x) ^^^ z = ((y ^^^ z) &&& x) ^^^ z := by ac_rfl
    _ = (x &&& y) + (~~~x &&& z) := choice_xor x y z

def aWord (h : BitVecState) (words : Array (BitVec 32)) (n : Nat) : BitVec 32 :=
  if n = 0 then h.d else if n = 1 then h.c else if n = 2 then h.b
  else (bitVecRounds h words (n - 3)).a

def eWord (h : BitVecState) (words : Array (BitVec 32)) (n : Nat) : BitVec 32 :=
  if n = 0 then h.h else if n = 1 then h.g else if n = 2 then h.f
  else (bitVecRounds h words (n - 3)).e

theorem rounds_words (h : BitVecState) (words : Array (BitVec 32)) (n : Nat) :
    bitVecRounds h words n =
      ⟨aWord h words (n+3), aWord h words (n+2), aWord h words (n+1), aWord h words n,
       eWord h words (n+3), eWord h words (n+2), eWord h words (n+1), eWord h words n⟩ := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    have ha : aWord h words (n + 1 + 3) = (bitVecRounds h words (n+1)).a := by
      have h0 : n + 1 + 3 ≠ 0 := by omega
      have h1 : n + 1 + 3 ≠ 1 := by omega
      have h2 : n + 1 + 3 ≠ 2 := by omega
      rw [aWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
        show n + 1 + 3 - 3 = n + 1 by omega]
    have he : eWord h words (n + 1 + 3) = (bitVecRounds h words (n+1)).e := by
      have h0 : n + 1 + 3 ≠ 0 := by omega
      have h1 : n + 1 + 3 ≠ 1 := by omega
      have h2 : n + 1 + 3 ≠ 2 := by omega
      rw [eWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
        show n + 1 + 3 - 3 = n + 1 by omega]
    rw [ha, he, bitVecRounds_succ, ih]
    rfl

theorem aWord_succ (h : BitVecState) (words : Array (BitVec 32)) (n : Nat) :
    aWord h words (n+4) =
      eWord h words n + bitVecBigSigma1 (eWord h words (n+3)) +
      bitVecChoice (eWord h words (n+3)) (eWord h words (n+2)) (eWord h words (n+1)) +
      SHA256.roundConstants[n]!.toBitVec + words[n]! +
      (bitVecBigSigma0 (aWord h words (n+3)) +
      bitVecMajority (aWord h words (n+3)) (aWord h words (n+2)) (aWord h words (n+1))) := by
  have h0 : n + 4 ≠ 0 := by omega
  have h1 : n + 4 ≠ 1 := by omega
  have h2 : n + 4 ≠ 2 := by omega
  rw [aWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, show n + 4 - 3 = n + 1 by omega,
    bitVecRounds_succ, rounds_words]
  rfl

theorem eWord_succ (h : BitVecState) (words : Array (BitVec 32)) (n : Nat) :
    eWord h words (n+4) = aWord h words n +
      (eWord h words n + bitVecBigSigma1 (eWord h words (n+3)) +
      bitVecChoice (eWord h words (n+3)) (eWord h words (n+2)) (eWord h words (n+1)) +
      SHA256.roundConstants[n]!.toBitVec + words[n]!) := by
  have h0 : n + 4 ≠ 0 := by omega
  have h1 : n + 4 ≠ 1 := by omega
  have h2 : n + 4 ≠ 2 := by omega
  rw [eWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, show n + 4 - 3 = n + 1 by omega,
    bitVecRounds_succ, rounds_words]
  rfl

def word (block : Array Bool) (n : Nat) : BitVec 32 := (schedule block)[n]!.toBitVec

def a (h : BitVecState) (block : Array Bool) (n : Nat) : BitVec 32 :=
  aWord h ((schedule block).map UInt32.toBitVec) (n+3)

def e (h : BitVecState) (block : Array Bool) (n : Nat) : BitVec 32 :=
  eWord h ((schedule block).map UInt32.toBitVec) (n+3)

theorem aWord_zero (h : BitVecState) (words : Array (BitVec 32)) : aWord h words 0 = h.d := rfl
theorem aWord_one (h : BitVecState) (words : Array (BitVec 32)) : aWord h words 1 = h.c := rfl
theorem aWord_two (h : BitVecState) (words : Array (BitVec 32)) : aWord h words 2 = h.b := rfl
theorem aWord_three (h : BitVecState) (words : Array (BitVec 32)) : aWord h words 3 = h.a := rfl
theorem eWord_zero (h : BitVecState) (words : Array (BitVec 32)) : eWord h words 0 = h.h := rfl
theorem eWord_one (h : BitVecState) (words : Array (BitVec 32)) : eWord h words 1 = h.g := rfl
theorem eWord_two (h : BitVecState) (words : Array (BitVec 32)) : eWord h words 2 = h.f := rfl
theorem eWord_three (h : BitVecState) (words : Array (BitVec 32)) : eWord h words 3 = h.e := rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
