import AesGcm.Proofs.Common.Detached

namespace AesGcm.Proofs.Machine.CTR

open Standards.NIST.GCM

private theorem fold_bits (bits : List Bool) (initial : Nat) :
    bits.foldl (fun n b ↦ 2 * n + b.toNat) initial =
      initial * 2 ^ bits.length + (BitVec.ofBoolListBE bits).toNat := by
  induction bits generalizing initial with
  | nil => simp [BitVec.ofBoolListBE]
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, BitVec.ofBoolListBE, BitVec.toNat_cons',
      Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.shiftLeft_eq, Nat.add_assoc]

theorem int_bitVec (x : BitVec n) :
    int (Vector.ofFn fun i : Fin n ↦ x.getMsbD i.val) = x.toNat := by
  rw [int, ← Vector.foldl_toList, fold_bits]
  simp only [Nat.zero_mul, Nat.zero_add]
  have h : (BitVec.ofBoolListBE (Vector.ofFn fun i : Fin n ↦ x.getMsbD i.val).toList).cast
      (by simp) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [Vector.toList_ofFn, BitVec.getMsbD_eq_getLsbD, hi, show n - 1 - (n - 1 - i) = i by omega]
  exact congrArg BitVec.toNat h

theorem inc_append_word (headBits : Vector Bool k) (word : BitVec s) :
    inc s (headBits ++ Vector.ofFn (fun i : Fin s ↦ word.getMsbD i.val)) =
      headBits ++ Vector.ofFn (fun i : Fin s ↦ (word + 1).getMsbD i.val) := by
  have hh : MSB k (headBits ++ Vector.ofFn (fun i : Fin s ↦ word.getMsbD i.val)) =
      headBits := by
    apply Vector.ext
    intro i hi
    simp [MSB, Vector.getElem_append_left]
  have hl : LSB s (headBits ++ Vector.ofFn (fun i : Fin s ↦ word.getMsbD i.val)) =
      Vector.ofFn (fun i : Fin s ↦ word.getMsbD i.val) := by
    apply Vector.ext
    intro i hi
    simp [LSB, Vector.getElem_append_right, Nat.le_add_right]
  rw [inc, hh, hl, int_bitVec]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [integerToString, Vector.getElem_ofFn, BitVec.getMsbD_eq_getLsbD,
    hi, decide_true, Bool.true_and, BitVec.getLsbD, BitVec.toNat_add]
  by_cases hs : s = 0
  · omega
  · have h1 : (1 : BitVec s).toNat = 1 := BitVec.toNat_one (by omega)
    rw [h1]

theorem repeat_inc_append_word (headBits : Vector Bool k) (word : BitVec s) (count : Nat) :
    Nat.repeat (inc s) count (headBits ++ Vector.ofFn (fun i : Fin s ↦ word.getMsbD i.val)) =
      headBits ++ Vector.ofFn (fun i : Fin s ↦
        (word + BitVec.ofNat s count).getMsbD i.val) := by
  induction count with
  | zero => simp [Nat.repeat]
  | succ count ih =>
    change inc s (Nat.repeat (inc s) count _) = _
    rw [ih, inc_append_word]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl

end AesGcm.Proofs.Machine.CTR
