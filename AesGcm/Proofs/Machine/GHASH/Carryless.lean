import AesGcm.Proofs.Machine.GHASH.Digits

namespace AesGcm.Proofs.Machine.GHASH

def maskedMul64 (x y : BitVec 64) : BitVec 64 :=
  let x0 := x &&& 0x1111111111111111
  let x1 := x &&& 0x2222222222222222
  let x2 := x &&& 0x4444444444444444
  let x3 := x &&& 0x8888888888888888
  let y0 := y &&& 0x1111111111111111
  let y1 := y &&& 0x2222222222222222
  let y2 := y &&& 0x4444444444444444
  let y3 := y &&& 0x8888888888888888
  let z0 := (x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)
  let z1 := (x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)
  let z2 := (x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)
  let z3 := (x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)
  (z0 &&& 0x1111111111111111) ||| (z1 &&& 0x2222222222222222) |||
    (z2 &&& 0x4444444444444444) ||| (z3 &&& 0x8888888888888888)

def carrylessMul64 (x y : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl (fun z i => if x.getLsbD i then z ^^^ (y <<< i) else z) 0

def carrylessPrefix (n : Nat) (x y : BitVec 64) : BitVec 64 :=
  (List.range n).foldl (fun z i => if x.getLsbD i then z ^^^ (y <<< i) else z) 0

theorem carrylessPrefix_zero (x y : BitVec 64) : carrylessPrefix 0 x y = 0 := rfl

theorem carrylessPrefix_succ (n : Nat) (x y : BitVec 64) :
    carrylessPrefix (n + 1) x y =
      carrylessPrefix n x y ^^^ (if x.getLsbD n then y <<< n else 0) := by
  simp only [carrylessPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  split <;> simp_all

theorem xor_left_comm (a b c : BitVec 64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem xor_cancel_left (a b : BitVec 64) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem carrylessPrefix_xor_left (n : Nat) (x y z : BitVec 64) :
    carrylessPrefix n (x ^^^ y) z = carrylessPrefix n x z ^^^ carrylessPrefix n y z := by
  induction n with
  | zero => simp [carrylessPrefix_zero]
  | succ n ih =>
    simp only [carrylessPrefix_succ, BitVec.getLsbD_xor, ih]
    cases hx : x.getLsbD n <;> cases hy : y.getLsbD n <;>
      simp [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, xor_cancel_left]

theorem carrylessPrefix_xor_right (n : Nat) (x y z : BitVec 64) :
    carrylessPrefix n x (y ^^^ z) = carrylessPrefix n x y ^^^ carrylessPrefix n x z := by
  induction n with
  | zero => simp [carrylessPrefix_zero]
  | succ n ih =>
    simp only [carrylessPrefix_succ, ih, BitVec.shiftLeft_xor_distrib]
    cases hx : x.getLsbD n <;>
      simp [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem carrylessPrefix_shift_right (n s : Nat) (x y : BitVec 64) :
    carrylessPrefix n x (y <<< s) = carrylessPrefix n x y <<< s := by
  induction n with
  | zero => simp [carrylessPrefix_zero]
  | succ n ih =>
    simp only [carrylessPrefix_succ, ih, BitVec.shiftLeft_xor_distrib]
    cases hx : x.getLsbD n <;> simp [← BitVec.shiftLeft_add, Nat.add_comm]

theorem carrylessPrefix_shift_left (n s : Nat) (x y : BitVec 64) (hn : n ≤ 64) :
    carrylessPrefix n (x <<< s) y = carrylessPrefix (n - s) x y <<< s := by
  induction n with
  | zero => simp [carrylessPrefix_zero]
  | succ n ih =>
    rw [carrylessPrefix_succ, ih (by omega)]
    by_cases hs : n < s
    · have he : n - s = 0 := by omega
      have he' : n + 1 - s = 0 := by omega
      simp [BitVec.getLsbD_shiftLeft, hs, he, he', carrylessPrefix_zero]
    · have he : n + 1 - s = n - s + 1 := by omega
      have hn' : n < 64 := by omega
      simp only [BitVec.getLsbD_shiftLeft, hn', decide_true, Bool.true_and,
        show ¬ n < s from hs, decide_false, Bool.not_false, Bool.true_and, he,
        carrylessPrefix_succ, BitVec.shiftLeft_xor_distrib]
      cases hx : x.getLsbD (n - s) <;>
        simp [← BitVec.shiftLeft_add, show n - s + s = n by omega]

theorem carrylessPrefix_shift_stable (n m s : Nat) (x y : BitVec 64)
    (hn : 64 ≤ n + s) (hm : n ≤ m) :
    carrylessPrefix m x y <<< s = carrylessPrefix n x y <<< s := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n; rfl
    have hnm : n ≤ m := by omega
    rw [carrylessPrefix_succ, BitVec.shiftLeft_xor_distrib, ih hnm]
    have hms : 64 ≤ m + s := by omega
    cases hx : x.getLsbD m <;> simp [← BitVec.shiftLeft_add, hms]

theorem carrylessMul64_shift_left (s : Nat) (x y : BitVec 64) :
    carrylessMul64 (x <<< s) y = carrylessMul64 x y <<< s := by
  change carrylessPrefix 64 (x <<< s) y = carrylessPrefix 64 x y <<< s
  rw [carrylessPrefix_shift_left 64 s x y (by omega)]
  exact (carrylessPrefix_shift_stable (64 - s) 64 s x y (by omega) (by omega)).symm

theorem carrylessPrefix_zero_left (n : Nat) (y : BitVec 64) :
    carrylessPrefix n (0#64) y = 0#64 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [carrylessPrefix_succ, ih]
    simp

theorem carrylessPrefix_one_left (n : Nat) (y : BitVec 64) :
    carrylessPrefix n (1#64) y = if n = 0 then 0#64 else y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [carrylessPrefix_succ, ih]
    cases n <;> simp [BitVec.getLsbD_ofNat, Nat.testBit_succ]

def xorCoeffs : List Nat → BitVec 64
  | [] => 0
  | x :: xs => BitVec.ofNat 64 (x % 2) ^^^ (xorCoeffs xs <<< 4)

theorem parity_add (a b : Nat) :
    BitVec.ofNat 64 ((a + b) % 2) =
      BitVec.ofNat 64 (a % 2) ^^^ BitVec.ofNat 64 (b % 2) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.add_mod, ha, hb]

theorem xorCoeffs_addCoeffs (xs ys : List Nat) :
    xorCoeffs (addCoeffs xs ys) = xorCoeffs xs ^^^ xorCoeffs ys := by
  induction xs generalizing ys with
  | nil => simp [addCoeffs, xorCoeffs]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoeffs, xorCoeffs]
    | cons y ys =>
      simp only [addCoeffs, xorCoeffs, parity_add, ih, BitVec.shiftLeft_xor_distrib]
      simp [BitVec.xor_assoc, xor_left_comm]

theorem xorCoeffs_map_zero (xs : List Nat) : xorCoeffs (xs.map (fun _ => 0)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [xorCoeffs, ih]

theorem xorCoeffs_mulCoeffs (xs ys : List Nat) (hx : ∀ n, coeff xs n ≤ 1) :
    xorCoeffs (mulCoeffs xs ys) = carrylessMul64 (xorCoeffs xs) (xorCoeffs ys) := by
  induction xs with
  | nil => exact (carrylessPrefix_zero_left 64 (xorCoeffs ys)).symm
  | cons x xs ih =>
    have hx0 : x = 0 ∨ x = 1 := by have := hx 0; change x ≤ 1 at this; omega
    have hxs : ∀ n, coeff xs n ≤ 1 := fun n => hx (n + 1)
    simp only [mulCoeffs, xorCoeffs_addCoeffs, xorCoeffs, ih hxs]
    change _ = carrylessPrefix 64 _ _
    rw [carrylessPrefix_xor_left]
    change _ = _ ^^^ carrylessMul64 (xorCoeffs xs <<< 4) (xorCoeffs ys)
    rw [carrylessMul64_shift_left]
    rcases hx0 with rfl | rfl
    · simp [xorCoeffs_map_zero, carrylessPrefix_zero_left]
    · simp [carrylessPrefix_one_left]

theorem testBit_of_le_one (a i : Nat) (ha : a ≤ 1) :
    a.testBit i = (decide (i = 0) && decide (a = 1)) := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl <;> cases i <;> simp [Nat.testBit_succ]

theorem getLsbD_parity (a i : Nat) (hi : i < 64) :
    (BitVec.ofNat 64 (a % 2)).getLsbD i = (decide (i = 0) && decide (a % 2 = 1)) := by
  rw [BitVec.getLsbD_ofNat, testBit_of_le_one (a % 2) i (by omega)]
  simp [hi]

theorem getLsbD_xorCoeffs (xs : List Nat) (i : Nat) (hi : i < 64) :
    (xorCoeffs xs).getLsbD i = (decide (i % 4 = 0) && decide (coeff xs (i / 4) % 2 = 1)) := by
  induction xs generalizing i with
  | nil => simp [xorCoeffs, coeff]
  | cons x xs ih =>
    simp only [xorCoeffs, BitVec.getLsbD_xor, getLsbD_parity x i hi,
      BitVec.getLsbD_shiftLeft]
    by_cases hi4 : i < 4
    · have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases he with rfl | rfl | rfl | rfl <;> simp [coeff]
    · have hz : i ≠ 0 := by omega
      have hsub : i - 4 < 64 := by omega
      have hm : (i - 4) % 4 = i % 4 := by omega
      have hd : i / 4 = (i - 4) / 4 + 1 := by omega
      simp only [hz, decide_false, Bool.false_and, Bool.false_xor, hi, decide_true,
        Bool.true_and, hi4, Bool.not_false, ih (i - 4) hsub, hm, hd, coeff]

def sparseDigits : Nat → BitVec 64 → List Nat
  | 0, _ => []
  | n + 1, x => (x.getLsbD 0).toNat :: sparseDigits n (x >>> 4)

theorem coeff_sparseDigits (n : Nat) (x : BitVec 64) (k : Nat) :
    coeff (sparseDigits n x) k = if k < n then (x.getLsbD (4 * k)).toNat else 0 := by
  induction n generalizing x k with
  | zero => simp [sparseDigits, coeff]
  | succ n ih =>
    cases k with
    | zero => simp [sparseDigits, coeff]
    | succ k =>
      simp only [sparseDigits, coeff, ih, BitVec.getLsbD_ushiftRight,
        Nat.succ_lt_succ_iff]
      congr 2
      congr 1
      omega

theorem coeff_sparseDigits_le (n : Nat) (x : BitVec 64) (k : Nat) :
    coeff (sparseDigits n x) k ≤ 1 := by
  rw [coeff_sparseDigits]
  split
  · cases x.getLsbD (4 * k) <;> decide
  · omega

def residueMask (r : Nat) : BitVec 64 := 0x1111111111111111 <<< r

theorem getLsbD_residueMask (r i : Nat) (hr : r < 4) (hi : i < 64) :
    (residueMask r).getLsbD i = decide (i % 4 = r) := by
  have h : ∀ r : Fin 4, ∀ i : Fin 64,
      (residueMask r.val).getLsbD i.val = decide (i.val % 4 = r.val) := by decide +kernel
  exact h ⟨r, hr⟩ ⟨i, hi⟩

theorem xorCoeffs_sparseDigits (x : BitVec 64) (r : Nat) (hr : r < 4) :
    xorCoeffs (sparseDigits 16 (x >>> r)) <<< r = x &&& residueMask r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, getLsbD_residueMask r i hr hi]
  by_cases hir : i < r
  · have he : i % 4 ≠ r := by omega
    simp [hi, hir, he]
  · have his : i - r < 64 := by omega
    have hk : (i - r) / 4 < 16 := by omega
    rw [getLsbD_xorCoeffs _ (i - r) his, coeff_sparseDigits]
    simp only [hk, ↓reduceIte, BitVec.getLsbD_ushiftRight, hi, decide_true,
      Bool.true_and, hir, decide_false, Bool.not_false]
    by_cases he : (i - r) % 4 = 0
    · have hm : i % 4 = r := by omega
      have hd : r + 4 * ((i - r) / 4) = i := by omega
      simp only [he, hm, hd, decide_true, Bool.true_and, Bool.and_true]
      cases x.getLsbD i <;> rfl
    · have hm : i % 4 ≠ r := by omega
      simp [he, hm]

theorem testBit_evalCoeffs (xs : List Nat) (n r : Nat) (hr : r < 4)
    (h : ∀ k < n, coeff xs k < 16) :
    (evalCoeffs 16 xs).testBit (4 * n + r) = (coeff xs n).testBit r := by
  rw [← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (4 * n) = 16 ^ n := by rw [Nat.pow_mul]
  rw [hp]
  have hmod := Nat.testBit_mod_two_pow (evalCoeffs 16 xs / 16 ^ n) 4 r
  have hc := Nat.testBit_mod_two_pow (coeff xs n) 4 r
  simp only [hr, decide_true, Bool.true_and] at hmod hc
  rw [← hmod, show 2 ^ 4 = 16 from rfl,
    evalCoeffs_div_pow_mod 16 16 (by decide) (by decide) xs n h]
  exact hc

theorem ofNat_evalCoeffs_eq_xorCoeffs (xs : List Nat) (hx : ∀ n, coeff xs n ≤ 1) :
    BitVec.ofNat 64 (evalCoeffs 16 xs) = xorCoeffs xs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, getLsbD_xorCoeffs xs i hi]
  simp only [hi, decide_true, Bool.true_and]
  have he : i = 4 * (i / 4) + i % 4 := by omega
  conv => lhs; rw [he]
  rw [testBit_evalCoeffs xs (i / 4) (i % 4) (by omega)
    (fun k _ => Nat.lt_of_le_of_lt (hx k) (by decide)), testBit_of_le_one _ _ (hx _)]
  rw [Nat.mod_eq_of_lt (show coeff xs (i / 4) < 2 by have := hx (i / 4); omega)]

theorem masked_evalCoeffs_product (xs ys : List Nat)
    (hx : ∀ n, coeff xs n ≤ 1) (hy : ∀ n, coeff ys n ≤ 1) (s : Nat) :
    (BitVec.ofNat 64 (evalCoeffs 16 xs * evalCoeffs 16 ys) <<< s) &&& residueMask (s % 4) =
      xorCoeffs (mulCoeffs xs ys) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    getLsbD_residueMask (s % 4) i (by omega) hi]
  by_cases his : i < s
  · simp [his]
  · have hk : i - s < 64 := by omega
    rw [BitVec.getLsbD_ofNat, getLsbD_xorCoeffs _ (i - s) hk]
    simp only [hi, hk, his, decide_true, decide_false, Bool.true_and, Bool.not_false]
    by_cases hm : (i - s) % 4 = 0
    · have hm' : i % 4 = s % 4 := by omega
      have he : i - s = 4 * ((i - s) / 4) := by omega
      simp only [hm, hm', decide_true, Bool.true_and, Bool.and_true]
      conv => lhs; rw [he]
      exact testBit_evalCoeffs_mulCoeffs xs ys hx hy ((i - s) / 4) (by omega)
    · have hm' : i % 4 ≠ s % 4 := by omega
      simp [hm, hm']

theorem shifted_mul (x y : BitVec 64) (r s : Nat) :
    (x <<< r) * (y <<< s) = (x * y) <<< (r + s) := by
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  rw [← BitVec.twoPow_mul_twoPow_eq]
  ac_rfl

theorem carrylessMul64_shift_right (s : Nat) (x y : BitVec 64) :
    carrylessMul64 x (y <<< s) = carrylessMul64 x y <<< s :=
  carrylessPrefix_shift_right 64 s x y

theorem masked_product (x y : BitVec 64) (r s : Nat) (hr : r < 4) (hs : s < 4) :
    ((x &&& residueMask r) * (y &&& residueMask s)) &&& residueMask ((r + s) % 4) =
      carrylessMul64 (x &&& residueMask r) (y &&& residueMask s) := by
  rw [← xorCoeffs_sparseDigits x r hr, ← xorCoeffs_sparseDigits y s hs, shifted_mul]
  rw [← ofNat_evalCoeffs_eq_xorCoeffs _ (coeff_sparseDigits_le 16 (x >>> r)),
    ← ofNat_evalCoeffs_eq_xorCoeffs _ (coeff_sparseDigits_le 16 (y >>> s)),
    ← BitVec.ofNat_mul, masked_evalCoeffs_product _ _
      (coeff_sparseDigits_le 16 (x >>> r)) (coeff_sparseDigits_le 16 (y >>> s))]
  rw [ofNat_evalCoeffs_eq_xorCoeffs _ (coeff_sparseDigits_le 16 (x >>> r)),
    ofNat_evalCoeffs_eq_xorCoeffs _ (coeff_sparseDigits_le 16 (y >>> s)),
    carrylessMul64_shift_left, xorCoeffs_mulCoeffs _ _ (coeff_sparseDigits_le 16 (x >>> r))]
  rw [carrylessMul64_shift_right, ← BitVec.shiftLeft_add, Nat.add_comm]

theorem and_xor_right (a b c : BitVec 64) :
    (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [Bool.and_xor_distrib_right]

theorem combineResidues (a b c d : BitVec 64) :
    (a &&& residueMask 0) ||| (b &&& residueMask 1) |||
      (c &&& residueMask 2) ||| (d &&& residueMask 3) =
    (a &&& residueMask 0) ^^^ (b &&& residueMask 1) ^^^
      (c &&& residueMask 2) ^^^ (d &&& residueMask 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_residueMask 0 i (by decide) hi, getLsbD_residueMask 1 i (by decide) hi,
    getLsbD_residueMask 2 i (by decide) hi, getLsbD_residueMask 3 i (by decide) hi]
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [h]

theorem splitResidues (x : BitVec 64) :
    x = (x &&& residueMask 0) ^^^ (x &&& residueMask 1) ^^^
      (x &&& residueMask 2) ^^^ (x &&& residueMask 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_residueMask 0 i (by decide) hi, getLsbD_residueMask 1 i (by decide) hi,
    getLsbD_residueMask 2 i (by decide) hi, getLsbD_residueMask 3 i (by decide) hi]
  have h : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [h]

theorem carrylessMul64_xor_left (x y z : BitVec 64) :
    carrylessMul64 (x ^^^ y) z = carrylessMul64 x z ^^^ carrylessMul64 y z :=
  carrylessPrefix_xor_left 64 x y z

theorem carrylessMul64_xor_right (x y z : BitVec 64) :
    carrylessMul64 x (y ^^^ z) = carrylessMul64 x y ^^^ carrylessMul64 x z :=
  carrylessPrefix_xor_right 64 x y z

theorem maskedMul64_eq_carrylessMul64 (x y : BitVec 64) :
    maskedMul64 x y = carrylessMul64 x y := by
  change ((((x &&& residueMask 0) * (y &&& residueMask 0)) ^^^ ((x &&& residueMask 1) * (y &&& residueMask 3)) ^^^ ((x &&& residueMask 2) * (y &&& residueMask 2)) ^^^ ((x &&& residueMask 3) * (y &&& residueMask 1))) &&& residueMask 0) |||
    ((((x &&& residueMask 0) * (y &&& residueMask 1)) ^^^ ((x &&& residueMask 1) * (y &&& residueMask 0)) ^^^ ((x &&& residueMask 2) * (y &&& residueMask 3)) ^^^ ((x &&& residueMask 3) * (y &&& residueMask 2))) &&& residueMask 1) |||
    ((((x &&& residueMask 0) * (y &&& residueMask 2)) ^^^ ((x &&& residueMask 1) * (y &&& residueMask 1)) ^^^ ((x &&& residueMask 2) * (y &&& residueMask 0)) ^^^ ((x &&& residueMask 3) * (y &&& residueMask 3))) &&& residueMask 2) |||
    ((((x &&& residueMask 0) * (y &&& residueMask 3)) ^^^ ((x &&& residueMask 1) * (y &&& residueMask 2)) ^^^ ((x &&& residueMask 2) * (y &&& residueMask 1)) ^^^ ((x &&& residueMask 3) * (y &&& residueMask 0))) &&& residueMask 3) = carrylessMul64 x y
  rw [combineResidues]
  simp only [and_xor_right]
  rw [masked_product x y 0 0 (by decide) (by decide)]
  rw [masked_product x y 1 3 (by decide) (by decide)]
  rw [masked_product x y 2 2 (by decide) (by decide)]
  rw [masked_product x y 3 1 (by decide) (by decide)]
  rw [masked_product x y 0 1 (by decide) (by decide)]
  rw [masked_product x y 1 0 (by decide) (by decide)]
  rw [masked_product x y 2 3 (by decide) (by decide)]
  rw [masked_product x y 3 2 (by decide) (by decide)]
  rw [masked_product x y 0 2 (by decide) (by decide)]
  rw [masked_product x y 1 1 (by decide) (by decide)]
  rw [masked_product x y 2 0 (by decide) (by decide)]
  rw [masked_product x y 3 3 (by decide) (by decide)]
  rw [masked_product x y 0 3 (by decide) (by decide)]
  rw [masked_product x y 1 2 (by decide) (by decide)]
  rw [masked_product x y 2 1 (by decide) (by decide)]
  rw [masked_product x y 3 0 (by decide) (by decide)]
  conv => rhs; rw [splitResidues x, splitResidues y]
  simp only [carrylessMul64_xor_left, carrylessMul64_xor_right]
  ac_rfl

end AesGcm.Proofs.Machine.GHASH
