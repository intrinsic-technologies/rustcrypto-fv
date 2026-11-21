import Std

namespace AesGcm.Proofs.Machine.GHASH

def addCoeffs : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addCoeffs xs ys

def mulCoeffs : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: xs, ys => addCoeffs (ys.map (x * ·)) (0 :: mulCoeffs xs ys)

def evalCoeffs (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + b * evalCoeffs b xs

def coeff : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => coeff xs n

theorem coeff_addCoeffs (xs ys : List Nat) (n : Nat) :
    coeff (addCoeffs xs ys) n = coeff xs n + coeff ys n := by
  induction xs generalizing ys n with
  | nil => simp [addCoeffs, coeff]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoeffs, coeff]
    | cons y ys =>
      cases n with
      | zero => rfl
      | succ n => exact ih ys n

theorem coeff_map_mul (xs : List Nat) (a n : Nat) :
    coeff (xs.map (a * ·)) n = a * coeff xs n := by
  induction xs generalizing n with
  | nil => simp [coeff]
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem evalCoeffs_addCoeffs (b : Nat) (xs ys : List Nat) :
    evalCoeffs b (addCoeffs xs ys) = evalCoeffs b xs + evalCoeffs b ys := by
  induction xs generalizing ys with
  | nil => simp [addCoeffs, evalCoeffs]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoeffs, evalCoeffs]
    | cons y ys =>
      simp only [addCoeffs, evalCoeffs, ih, Nat.mul_add]
      omega

theorem evalCoeffs_map_mul (b a : Nat) (xs : List Nat) :
    evalCoeffs b (xs.map (a * ·)) = a * evalCoeffs b xs := by
  induction xs with
  | nil => simp [evalCoeffs]
  | cons x xs ih =>
    simp only [List.map_cons, evalCoeffs, ih]
    grind

theorem evalCoeffs_mulCoeffs (b : Nat) (xs ys : List Nat) :
    evalCoeffs b (mulCoeffs xs ys) = evalCoeffs b xs * evalCoeffs b ys := by
  induction xs with
  | nil => simp [mulCoeffs, evalCoeffs]
  | cons x xs ih =>
    simp only [mulCoeffs, evalCoeffs_addCoeffs, evalCoeffs_map_mul, evalCoeffs, ih]
    grind

theorem coeff_mulCoeffs_le (xs ys : List Nat)
    (hx : ∀ n, coeff xs n ≤ 1) (hy : ∀ n, coeff ys n ≤ 1) (n : Nat) :
    coeff (mulCoeffs xs ys) n ≤ n + 1 := by
  induction xs generalizing n with
  | nil => simp [mulCoeffs, coeff]
  | cons x xs ih =>
    have hxs : ∀ k, coeff xs k ≤ 1 := fun k => hx (k + 1)
    have hx0 : x ≤ 1 := hx 0
    simp only [mulCoeffs, coeff_addCoeffs, coeff_map_mul]
    have hp : x * coeff ys n ≤ 1 := by
      have := Nat.mul_le_mul hx0 (hy n)
      simpa using this
    cases n with
    | zero => simpa [coeff] using hp
    | succ n =>
      have hi := ih hxs n
      simp only [coeff]
      omega

theorem evalCoeffs_div_pow_mod (b d : Nat) (hb : 0 < b) (hd : b % d = 0)
    (xs : List Nat) (n : Nat) (h : ∀ k < n, coeff xs k < b) :
    evalCoeffs b xs / b ^ n % d = coeff xs n % d := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [evalCoeffs, coeff]
    | cons x xs => simp [evalCoeffs, coeff, Nat.add_mod, Nat.mul_mod, hd]
  | succ n ih =>
    cases xs with
    | nil => simp [evalCoeffs, coeff]
    | cons x xs =>
      have hx : x < b := h 0 (by omega)
      have ht : ∀ k < n, coeff xs k < b := fun k hk => h (k + 1) (by omega)
      rw [evalCoeffs, Nat.pow_succ, Nat.mul_comm (b ^ n), ← Nat.div_div_eq_div_mul]
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hx, Nat.zero_add]
      exact ih xs ht

theorem testBit_evalCoeffs_mulCoeffs (xs ys : List Nat)
    (hx : ∀ n, coeff xs n ≤ 1) (hy : ∀ n, coeff ys n ≤ 1)
    (n : Nat) (hn : n < 16) :
    (evalCoeffs 16 xs * evalCoeffs 16 ys).testBit (4 * n) =
      decide (coeff (mulCoeffs xs ys) n % 2 = 1) := by
  rw [← evalCoeffs_mulCoeffs, Nat.testBit_eq_decide_div_mod_eq]
  have hp : 2 ^ (4 * n) = 16 ^ n := by rw [Nat.pow_mul]
  rw [hp, evalCoeffs_div_pow_mod 16 2 (by decide) (by decide)]
  intro k hk
  have hc := coeff_mulCoeffs_le xs ys hx hy k
  omega

end AesGcm.Proofs.Machine.GHASH
