import AesGcm.Proofs.Machine.GHASH.Carryless

namespace AesGcm.Proofs.Machine.GHASH

def xorSum {w : Nat} (xs : List (BitVec w)) : BitVec w := xs.foldr (· ^^^ ·) 0

theorem xorSum_append {w : Nat} (xs ys : List (BitVec w)) :
    xorSum (xs ++ ys) = xorSum xs ^^^ xorSum ys := by
  induction xs with
  | nil => simp [xorSum]
  | cons x xs ih =>
    change x ^^^ xorSum (xs ++ ys) = (x ^^^ xorSum xs) ^^^ xorSum ys
    rw [ih, BitVec.xor_assoc]

theorem xorSum_map_hom {v w : Nat} (h : BitVec v → BitVec w)
    (hzero : h 0 = 0) (hxor : ∀ x y, h (x ^^^ y) = h x ^^^ h y)
    (xs : List (BitVec v)) : xorSum (xs.map h) = h (xorSum xs) := by
  induction xs with
  | nil => exact hzero.symm
  | cons x xs ih => simp only [List.map_cons, xorSum, List.foldr_cons] at *; rw [ih, hxor]

theorem xorSum_reverse {w : Nat} (xs : List (BitVec w)) : xorSum xs.reverse = xorSum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, xorSum_append, ih]
    simp [xorSum, BitVec.xor_comm]

def wideMul64 (x y : BitVec 64) : BitVec 128 :=
  xorSum ((List.range 64).map (fun i => if x.getLsbD i then (y.setWidth 128) <<< i else 0))

def high64 (x : BitVec 128) : BitVec 64 := (x >>> 64).setWidth 64

def reverseShift (x : BitVec 64) : BitVec 64 := x.reverse >>> 1

theorem high64_xor (x y : BitVec 128) : high64 (x ^^^ y) = high64 x ^^^ high64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [high64, BitVec.getLsbD_ushiftRight, hi]

theorem reverseShift_xor (x y : BitVec 64) :
    reverseShift (x ^^^ y) = reverseShift x ^^^ reverseShift y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [reverseShift, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD, Bool.and_xor_distrib_left]

theorem high64_shift_term (y : BitVec 64) (j : Nat) (hj : j < 64) :
    high64 ((y.setWidth 128) <<< j) = reverseShift (y.reverse <<< (63 - j)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [high64, reverseShift, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  have h1 : 64 + i < 128 := by omega
  have h2 : ¬64 + i < j := by omega
  have hwide : 64 + i - j < 128 := by omega
  simp only [hi, h1, h2, decide_true, decide_false, Bool.true_and, Bool.not_false]
  by_cases hi' : i + 1 < 64
  · have h3 : 64 - 1 - (1 + i) < 64 := by omega
    have h4 : (64 - 1 - (1 + i) - (63 - j)) < 64 := by omega
    have h5 : 1 + i < 64 := by omega
    simp only [h3, h4, h5, decide_true, Bool.true_and]
    by_cases hij : i < j
    · have h6 : 64 + i - j < 64 := by omega
      have h7 : ¬64 - 1 - (1 + i) < 63 - j := by omega
      have h8 : 64 - 1 - (64 - 1 - (1 + i) - (63 - j)) = 64 + i - j := by omega
      simp [h6, h7, h8, hwide]
    · have h6 : ¬64 + i - j < 64 := by omega
      have h7 : 64 - 1 - (1 + i) < 63 - j := by omega
      simp [h7, BitVec.getLsbD_of_ge y (64 + i - j) (by omega)]
  · have h3 : ¬1 + i < 64 := by omega
    have h4 : ¬64 + i - j < 64 := by omega
    simp [h3, BitVec.getLsbD_of_ge y (64 + i - j) (by omega)]

theorem xorSum_range_carryless (n : Nat) (x y : BitVec 64) :
    xorSum ((List.range n).map (fun i => if x.getLsbD i then y <<< i else 0)) =
      carrylessPrefix n x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, xorSum_append, ih, carrylessPrefix_succ]
    simp [xorSum]

theorem wideMul64_low (x y : BitVec 64) : (wideMul64 x y).setWidth 64 = carrylessMul64 x y := by
  rw [wideMul64, ← xorSum_map_hom (fun z : BitVec 128 => z.setWidth 64)
    (by rfl) (fun _ _ => BitVec.setWidth_xor)]
  rw [List.map_map]
  change xorSum _ = carrylessPrefix 64 x y
  rw [← xorSum_range_carryless]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  split <;> simp [BitVec.setWidth_shiftLeft_of_le]

theorem wideMul64_high (x y : BitVec 64) :
    high64 (wideMul64 x y) = reverseShift (carrylessMul64 x.reverse y.reverse) := by
  have hz : high64 (0#128) = 0#64 := by rfl
  have hrz : reverseShift (0#64) = 0#64 := by decide +kernel
  have hm : (List.range 64).map (fun i => 63 - i) = (List.range 64).reverse := by
    decide +kernel
  rw [wideMul64, ← xorSum_map_hom high64 hz high64_xor]
  change _ = reverseShift (carrylessPrefix 64 x.reverse y.reverse)
  rw [← xorSum_range_carryless, ← xorSum_map_hom reverseShift hrz reverseShift_xor]
  rw [List.map_map, List.map_map]
  let f := fun i => reverseShift (if x.reverse.getLsbD i then y.reverse <<< i else 0)
  have he :
      (List.range 64).map (fun i => high64 (if x.getLsbD i then y.setWidth 128 <<< i else 0)) =
        ((List.range 64).map (fun i => 63 - i)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < 64 := List.mem_range.mp hi
    have hrev : x.reverse.getLsbD (63 - i) = x.getLsbD i := by
      rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
      simp [show 63 - i < 64 by omega, show 64 - 1 - (63 - i) = i by omega]
    change high64 (if x.getLsbD i then y.setWidth 128 <<< i else 0) =
      reverseShift (if x.reverse.getLsbD (63 - i) then y.reverse <<< (63 - i) else 0)
    rw [hrev]
    cases hxi : x.getLsbD i
    · exact hz.trans hrz.symm
    · exact high64_shift_term y i hi'
  change xorSum ((List.range 64).map (fun i =>
    high64 (if x.getLsbD i then y.setWidth 128 <<< i else 0))) = xorSum ((List.range 64).map f)
  rw [he, hm, List.map_reverse, xorSum_reverse]

theorem wideMul64_low_masked (x y : BitVec 64) :
    (wideMul64 x y).setWidth 64 = maskedMul64 x y := by
  rw [wideMul64_low, maskedMul64_eq_carrylessMul64]

theorem wideMul64_high_masked (x y : BitVec 64) :
    high64 (wideMul64 x y) = (maskedMul64 x.reverse y.reverse).reverse >>> 1 := by
  rw [wideMul64_high, maskedMul64_eq_carrylessMul64]
  rfl

theorem getLsbD_xorSum_false {w : Nat} (xs : List (BitVec w)) (i : Nat)
    (h : ∀ x ∈ xs, x.getLsbD i = false) : (xorSum xs).getLsbD i = false := by
  induction xs with
  | nil => simp [xorSum]
  | cons x xs ih =>
    change (x ^^^ xorSum xs).getLsbD i = false
    rw [BitVec.getLsbD_xor, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem wideMul64_high_msb (x y : BitVec 64) : (high64 (wideMul64 x y)).getLsbD 63 = false := by
  simp only [high64, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    Nat.reduceLT, Nat.reduceAdd, decide_true, Bool.true_and]
  apply getLsbD_xorSum_false
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have hi' : i < 64 := List.mem_range.mp hi
  split
  · simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rw [BitVec.getLsbD_of_ge y (127 - i) (by omega)]
    simp
  · simp

theorem shiftLeft_one_ushiftRight_one (x : BitVec 64) (h : x.getLsbD 63 = false) :
    (x <<< (1 : Nat)) >>> (1 : Nat) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hs : 1 + i < 64
  · simp [hs]
  · have he : i = 63 := by omega
    subst i
    simp only [Nat.reduceAdd, Nat.reduceLT, decide_false, Bool.false_and]
    exact h.symm

theorem wideMul64_high_double_half (x y : BitVec 64) :
    (high64 (wideMul64 x y) <<< (1 : Nat)) >>> (1 : Nat) = high64 (wideMul64 x y) :=
  shiftLeft_one_ushiftRight_one _ (wideMul64_high_msb x y)

end AesGcm.Proofs.Machine.GHASH
