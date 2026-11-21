import K256.Proofs.Common.Field.Repr
import K256.Proofs.Common.Field.PowMod

namespace K256.Proofs.Common.Field.SqrtChain

inductive Step where
  | sqr (src k : Nat)
  | mul (a b : Nat)
  deriving DecidableEq, Repr

def iter {α : Type} (g : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iter g k (g a)

def Step.apply {α : Type} (sq : α → α) (mul : α → α → α) (d : α) (vs : List α) : Step → α
  | .sqr i k => iter sq k (vs.getD i d)
  | .mul i j => mul (vs.getD i d) (vs.getD j d)

def runFrom {α : Type} (sq : α → α) (mul : α → α → α) (d : α) (vs : List α) : List Step → List α
  | [] => vs
  | s :: ss => runFrom sq mul d (vs ++ [s.apply sq mul d vs]) ss

def run {α : Type} (sq : α → α) (mul : α → α → α) (x : α) (steps : List Step) : List α :=
  runFrom sq mul x [x] steps

def result {α : Type} (sq : α → α) (mul : α → α → α) (x : α) (steps : List Step) : α :=
  (run sq mul x steps).getD steps.length x

def chain : List Step :=
  [ .sqr 0 1, .mul 0 1,
    .sqr 2 1, .mul 0 3,
    .sqr 4 3, .mul 4 5,
    .sqr 6 3, .mul 4 7,
    .sqr 8 2, .mul 2 9,
    .sqr 10 11, .mul 10 11,
    .sqr 12 22, .mul 12 13,
    .sqr 14 44, .mul 14 15,
    .sqr 16 88, .mul 16 17,
    .sqr 18 44, .mul 14 19,
    .sqr 20 3, .mul 4 21,
    .sqr 22 23, .mul 12 23,
    .sqr 24 6, .mul 2 25,
    .sqr 26 2 ]

def exponent : Nat := result (fun e => 2 * e) (· + ·) 1 chain

theorem exponent_eq : exponent = (modulus + 1) / 4 := by
  decide +kernel

theorem iterate_comm {α β : Type} (f : α → β) (g : α → α) (g' : β → β)
    (h : ∀ a, f (g a) = g' (f a)) : ∀ (k : Nat) (a : α), f (iter g k a) = iter g' k (f a)
  | 0, _ => rfl
  | k + 1, a => by
    simp only [iter]
    rw [iterate_comm f g g' h k, h]

theorem getD_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD]

theorem runFrom_map {α β : Type} (f : α → β) (sq : α → α) (mul : α → α → α) (d : α)
    (sq' : β → β) (mul' : β → β → β)
    (hsq : ∀ a, f (sq a) = sq' (f a)) (hmul : ∀ a b, f (mul a b) = mul' (f a) (f b)) :
    ∀ (steps : List Step) (vs : List α),
      (runFrom sq mul d vs steps).map f = runFrom sq' mul' (f d) (vs.map f) steps
  | [], _ => rfl
  | s :: ss, vs => by
    simp only [runFrom]
    rw [runFrom_map f sq mul d sq' mul' hsq hmul ss, List.map_append]
    congr 2
    cases s with
    | sqr i k => simp only [Step.apply, List.map_cons, List.map_nil, iterate_comm f sq sq' hsq, getD_map]
    | mul i j => simp only [Step.apply, List.map_cons, List.map_nil, hmul, getD_map]

theorem run_map {α β : Type} (f : α → β) (sq : α → α) (mul : α → α → α) (x : α)
    (sq' : β → β) (mul' : β → β → β)
    (hsq : ∀ a, f (sq a) = sq' (f a)) (hmul : ∀ a b, f (mul a b) = mul' (f a) (f b))
    (steps : List Step) :
    (run sq mul x steps).map f = run sq' mul' (f x) steps :=
  runFrom_map f sq mul x sq' mul' hsq hmul steps [x]

theorem result_map {α β : Type} (f : α → β) (sq : α → α) (mul : α → α → α) (x : α)
    (sq' : β → β) (mul' : β → β → β)
    (hsq : ∀ a, f (sq a) = sq' (f a)) (hmul : ∀ a b, f (mul a b) = mul' (f a) (f b))
    (steps : List Step) :
    f (result sq mul x steps) = result sq' mul' (f x) steps := by
  unfold result
  rw [← run_map f sq mul x sq' mul' hsq hmul steps, getD_map]

def modSq (a : Nat) : Nat := a * a % modulus

def modMul (a b : Nat) : Nat := a * b % modulus

theorem result_modPow (x : Nat) :
    result modSq modMul (x % modulus) chain = x ^ ((modulus + 1) / 4) % modulus := by
  have h := result_map (fun e => x ^ e % modulus) (fun e => 2 * e) (· + ·) 1 modSq modMul
    (fun a => by
      simp only [modSq]
      rw [Nat.mul_comm 2 a, Nat.pow_mul, Nat.pow_two, Nat.mul_mod])
    (fun a b => by
      simp only [modMul]
      rw [Nat.pow_add, Nat.mul_mod])
    chain
  simp only [Nat.pow_one] at h
  rw [← h]
  show x ^ exponent % modulus = _
  rw [exponent_eq]

theorem result_sqrt (x : Fin modulus) :
    result modSq modMul x.val chain = x.val ^ ((modulus + 1) / 4) % modulus := by
  have := result_modPow x.val
  rwa [Nat.mod_eq_of_lt x.isLt] at this

theorem sqrtMod_eq (x : Nat) :
    K256.Spec.Secp256k1.sqrtMod x =
      let r := result modSq modMul (x % modulus) chain
      if modSq r = x % modulus then some r else none := by
  simp only [result_modPow]
  simp only [K256.Spec.Secp256k1.sqrtMod, Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4,
    PowMod.powMod_eq_pow_mod, modSq, modulus, beq_iff_eq]
  split <;> simp_all

end K256.Proofs.Common.Field.SqrtChain
