import AesGcm.Proofs.Machine.GHASH.Montgomery
import AesGcm.Proofs.Machine.GHASH.ReductionWords

namespace AesGcm.Proofs.Machine.GHASH

theorem xorSum_map_xor {α : Type} {w : Nat} (is : List α) (f g : α → BitVec w) :
    xorSum (is.map (fun i => f i ^^^ g i)) = xorSum (is.map f) ^^^ xorSum (is.map g) := by
  induction is with
  | nil => simp [xorSum]
  | cons i is ih =>
    change (f i ^^^ g i) ^^^ xorSum (is.map (fun j => f j ^^^ g j)) =
      (f i ^^^ xorSum (is.map f)) ^^^ (g i ^^^ xorSum (is.map g))
    rw [ih]
    ac_rfl

def shiftSum {m w : Nat} (n : Nat) (x : BitVec m) (y : BitVec w) : BitVec w :=
  xorSum ((List.range n).map (fun i => if x.getLsbD i then y <<< i else 0))

theorem shiftSum_xor_right {m w : Nat} (n : Nat) (x : BitVec m) (y z : BitVec w) :
    shiftSum n x (y ^^^ z) = shiftSum n x y ^^^ shiftSum n x z := by
  unfold shiftSum
  rw [← xorSum_map_xor]
  congr 1
  apply List.map_congr_left
  intro i _
  cases x.getLsbD i <;> simp [BitVec.shiftLeft_xor_distrib]

theorem shiftSum_xor_left {m w : Nat} (n : Nat) (x z : BitVec m) (y : BitVec w) :
    shiftSum n (x ^^^ z) y = shiftSum n x y ^^^ shiftSum n z y := by
  unfold shiftSum
  rw [← xorSum_map_xor]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases z.getLsbD i <;> simp

theorem shiftSum_shift_right {m w : Nat} (n s : Nat) (x : BitVec m) (y : BitVec w) :
    shiftSum n x (y <<< s) = shiftSum n x y <<< s := by
  rw [shiftSum, shiftSum, ← xorSum_map_hom (fun z : BitVec w => z <<< s)
    (by simp) (fun a b => BitVec.shiftLeft_xor_distrib a b s), List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  cases h : x.getLsbD i <;> simp [h, ← BitVec.shiftLeft_add, Nat.add_comm]

theorem extend_shift64 (y : BitVec 64) (i : Nat) (hi : i < 64) :
    (y.setWidth 128 <<< i).setWidth 256 = y.setWidth 256 <<< i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
  by_cases h : j < 128
  · simp [h, show j - i < 128 from by omega, show j - i < 256 from by omega]
  · have hz : y.getLsbD (j - i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [hz]

theorem wideMul64_extend (x y : BitVec 64) :
    (wideMul64 x y).setWidth 256 = shiftSum 64 x (y.setWidth 256) := by
  rw [wideMul64, ← xorSum_map_hom (fun z : BitVec 128 => z.setWidth 256)
    (by rfl) (fun _ _ => BitVec.setWidth_xor), List.map_map]
  unfold shiftSum
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < 64 := List.mem_range.mp hi
  change (if x.getLsbD i then y.setWidth 128 <<< i else 0#128).setWidth 256 = _
  cases x.getLsbD i
  · rfl
  · exact extend_shift64 y i hi'

theorem append64_extend (lo hi : BitVec 64) :
    (hi ++ lo).setWidth 256 = lo.setWidth 256 ^^^ (hi.setWidth 256 <<< (64 : Nat)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft]
  grind

theorem shiftSum_append_left {m n w : Nat} (lo : BitVec m) (hi : BitVec n) (y : BitVec w) :
    shiftSum (m + n) (hi ++ lo) y = shiftSum m lo y ^^^ (shiftSum n hi y <<< m) := by
  have hr : List.range (m + n) = List.range m ++ (List.range n).map (fun i => m + i) := by
    exact List.range_add
  unfold shiftSum
  rw [hr, List.map_append, xorSum_append, List.map_map]
  apply congr (congrArg (fun a : BitVec w => fun b : BitVec w => a ^^^ b) ?_) ?_
  · congr 1
    apply List.map_congr_left
    intro i hi
    simp only [BitVec.getLsbD_append, List.mem_range.mp hi, ite_true]
  · rw [← xorSum_map_hom (fun z : BitVec w => z <<< m)
      (by simp) (fun a b => BitVec.shiftLeft_xor_distrib a b m), List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi'
    change (if (hi ++ lo).getLsbD (m + i) then y <<< (m + i) else 0#w) =
      (if hi.getLsbD i then y <<< i else 0#w) <<< m
    simp only [BitVec.getLsbD_append, show ¬m + i < m from by omega,
      show m + i - m = i from by omega, ite_false]
    cases hi.getLsbD i <;> simp [← BitVec.shiftLeft_add, Nat.add_comm]

theorem wideMul128_four_products (x0 x1 y0 y1 : BitVec 64) :
    wideMul128 (x1 ++ x0) (y1 ++ y0) =
      (wideMul64 x0 y0).setWidth 256 ^^^
      ((wideMul64 x0 y1).setWidth 256 <<< (64 : Nat)) ^^^
      ((wideMul64 x1 y0).setWidth 256 <<< (64 : Nat)) ^^^
      ((wideMul64 x1 y1).setWidth 256 <<< (128 : Nat)) := by
  change shiftSum 128 (x1 ++ x0) ((y1 ++ y0).setWidth 256) = _
  rw [shiftSum_append_left x0 x1, append64_extend]
  rw [shiftSum_xor_right, shiftSum_xor_right, shiftSum_shift_right,
    shiftSum_shift_right, ← wideMul64_extend, ← wideMul64_extend,
    ← wideMul64_extend, ← wideMul64_extend]
  generalize wideMul64 x0 y0 = p, wideMul64 x0 y1 = r,
    wideMul64 x1 y0 = s, wideMul64 x1 y1 = q
  rw [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
  exact (BitVec.xor_assoc _ _ _).symm

theorem wideMul64_xor_left (x z y : BitVec 64) :
    wideMul64 (x ^^^ z) y = wideMul64 x y ^^^ wideMul64 z y :=
  shiftSum_xor_left 64 x z (y.setWidth 128)

theorem wideMul64_xor_right (x y z : BitVec 64) :
    wideMul64 x (y ^^^ z) = wideMul64 x y ^^^ wideMul64 x z := by
  change shiftSum 64 x ((y ^^^ z).setWidth 128) = _
  rw [BitVec.setWidth_xor]
  exact shiftSum_xor_right 64 x (y.setWidth 128) (z.setWidth 128)

theorem wideMul64_cross (x0 x1 y0 y1 : BitVec 64) :
    wideMul64 x0 y1 ^^^ wideMul64 x1 y0 =
      wideMul64 (x0 ^^^ x1) (y0 ^^^ y1) ^^^ wideMul64 x0 y0 ^^^ wideMul64 x1 y1 := by
  rw [wideMul64_xor_left, wideMul64_xor_right, wideMul64_xor_right]
  generalize wideMul64 x0 y0 = p, wideMul64 x0 y1 = r,
    wideMul64 x1 y0 = s, wideMul64 x1 y1 = q
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_xor, Bool.xor_left_comm, Bool.xor_comm]

theorem wideMul128_karatsuba (x0 x1 y0 y1 : BitVec 64) :
    wideMul128 (x1 ++ x0) (y1 ++ y0) =
      (wideMul64 x0 y0).setWidth 256 ^^^
      ((wideMul64 (x0 ^^^ x1) (y0 ^^^ y1) ^^^ wideMul64 x0 y0 ^^^ wideMul64 x1 y1).setWidth 256 <<< (64 : Nat)) ^^^
      ((wideMul64 x1 y1).setWidth 256 <<< (128 : Nat)) := by
  rw [wideMul128_four_products, ← wideMul64_cross]
  generalize wideMul64 x0 y0 = p, wideMul64 x0 y1 = r,
    wideMul64 x1 y0 = s, wideMul64 x1 y1 = q
  rw [BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]
  exact congrArg (fun z => z ^^^ q.setWidth 256 <<< (128 : Nat))
    (BitVec.xor_assoc _ _ _)

set_option maxRecDepth 1024 in
theorem joinWords_karatsuba (p q t : BitVec 128) :
    p.setWidth 256 ^^^ ((t ^^^ p ^^^ q).setWidth 256 <<< (64 : Nat)) ^^^
      (q.setWidth 256 <<< (128 : Nat)) =
      joinWords (p.setWidth 64)
        (t.setWidth 64 ^^^ p.setWidth 64 ^^^ q.setWidth 64 ^^^ high64 p)
        (q.setWidth 64 ^^^ high64 p ^^^ high64 q ^^^ high64 t) (high64 q) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [joinWords, high64, BitVec.getLsbD_append, BitVec.getLsbD_xor,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h0 : i < 64
  · grind
  · by_cases h1 : i < 128
    · grind
    · by_cases h2 : i < 192 <;> grind

theorem wideMul128_words (x0 x1 y0 y1 : BitVec 64) :
    wideMul128 (x1 ++ x0) (y1 ++ y0) =
      let p := wideMul64 x0 y0
      let q := wideMul64 x1 y1
      let t := wideMul64 (x0 ^^^ x1) (y0 ^^^ y1)
      joinWords (p.setWidth 64)
        (t.setWidth 64 ^^^ p.setWidth 64 ^^^ q.setWidth 64 ^^^ high64 p)
        (q.setWidth 64 ^^^ high64 p ^^^ high64 q ^^^ high64 t) (high64 q) := by
  rw [wideMul128_karatsuba, joinWords_karatsuba]


end AesGcm.Proofs.Machine.GHASH
