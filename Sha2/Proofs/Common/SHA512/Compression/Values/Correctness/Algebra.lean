import Sha2.Proofs.Common.SHA512.Compression.Values.Program
import Sha2.Proofs.Common.SHA512.Compression.Values.Registers
import Sha2.Proofs.Common.SHA512.Compression.InputWords

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.NIST

theorem choice_xor (x y z : BitVec 64) :
    ((y ^^^ z) &&& x) ^^^ z = (x &&& y) + (~~~x &&& z) := by
  rw [← bitVecChoice_eq_and_xor, ← bitVecChoice_eq_add_and]

theorem choice_xor_commuted (x y z : BitVec 64) :
    ((z ^^^ y) &&& x) ^^^ z = (x &&& y) + (~~~x &&& z) := by
  calc
    ((z ^^^ y) &&& x) ^^^ z = ((y ^^^ z) &&& x) ^^^ z := by ac_rfl
    _ = (x &&& y) + (~~~x &&& z) := choice_xor x y z

theorem majority_xor (x y z : BitVec 64) :
    ((y ^^^ z) &&& x) ^^^ (y &&& z) = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  calc
    ((y ^^^ z) &&& x) ^^^ (y &&& z) = bitVecMajority x y z :=
      (bitVecMajority_eq_and_xor x y z).symm
    _ = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := rfl

def aWord (h : BitVecState) (words : Array (BitVec 64)) (n : Nat) : BitVec 64 :=
  if n = 0 then h.d else if n = 1 then h.c else if n = 2 then h.b
  else (bitVecRounds h words (n - 3)).a

def eWord (h : BitVecState) (words : Array (BitVec 64)) (n : Nat) : BitVec 64 :=
  if n = 0 then h.h else if n = 1 then h.g else if n = 2 then h.f
  else (bitVecRounds h words (n - 3)).e

theorem rounds_words (h : BitVecState) (words : Array (BitVec 64)) (n : Nat) :
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

theorem aWord_succ (h : BitVecState) (words : Array (BitVec 64)) (n : Nat) :
    aWord h words (n+4) =
      (eWord h words n + bitVecBigSigma1 (eWord h words (n+3)) +
        bitVecChoice (eWord h words (n+3)) (eWord h words (n+2)) (eWord h words (n+1)) +
        SHA512.roundConstants[n]!.toBitVec + words[n]!) +
      (bitVecBigSigma0 (aWord h words (n+3)) +
        bitVecMajority (aWord h words (n+3)) (aWord h words (n+2)) (aWord h words (n+1))) := by
  have h0 : n + 4 ≠ 0 := by omega
  have h1 : n + 4 ≠ 1 := by omega
  have h2 : n + 4 ≠ 2 := by omega
  rw [aWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
    show n + 4 - 3 = n + 1 by omega, bitVecRounds_succ, rounds_words]
  rfl

theorem eWord_succ (h : BitVecState) (words : Array (BitVec 64)) (n : Nat) :
    eWord h words (n+4) = aWord h words n +
      (eWord h words n + bitVecBigSigma1 (eWord h words (n+3)) +
        bitVecChoice (eWord h words (n+3)) (eWord h words (n+2)) (eWord h words (n+1)) +
        SHA512.roundConstants[n]!.toBitVec + words[n]!) := by
  have h0 : n + 4 ≠ 0 := by omega
  have h1 : n + 4 ≠ 1 := by omega
  have h2 : n + 4 ≠ 2 := by omega
  rw [eWord, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
    show n + 4 - 3 = n + 1 by omega, bitVecRounds_succ, rounds_words]
  rfl

theorem aWord_zero (h : BitVecState) (words : Array (BitVec 64)) : aWord h words 0 = h.d := rfl
theorem aWord_one (h : BitVecState) (words : Array (BitVec 64)) : aWord h words 1 = h.c := rfl
theorem aWord_two (h : BitVecState) (words : Array (BitVec 64)) : aWord h words 2 = h.b := rfl
theorem aWord_three (h : BitVecState) (words : Array (BitVec 64)) : aWord h words 3 = h.a := rfl
theorem eWord_zero (h : BitVecState) (words : Array (BitVec 64)) : eWord h words 0 = h.h := rfl
theorem eWord_one (h : BitVecState) (words : Array (BitVec 64)) : eWord h words 1 = h.g := rfl
theorem eWord_two (h : BitVecState) (words : Array (BitVec 64)) : eWord h words 2 = h.f := rfl
theorem eWord_three (h : BitVecState) (words : Array (BitVec 64)) : eWord h words 3 = h.e := rfl

def word (block : Array Bool) (n : Nat) : BitVec 64 :=
  (schedule block)[n]!.toBitVec

def a (h : BitVecState) (block : Array Bool) (n : Nat) : BitVec 64 :=
  aWord h ((schedule block).map UInt64.toBitVec) (n+3)

def e (h : BitVecState) (block : Array Bool) (n : Nat) : BitVec 64 :=
  eWord h ((schedule block).map UInt64.toBitVec) (n+3)

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
