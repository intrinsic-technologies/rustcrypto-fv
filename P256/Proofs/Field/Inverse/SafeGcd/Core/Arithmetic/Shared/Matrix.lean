import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd

structure Matrix where
  u : Int
  v : Int
  q : Int
  r : Int
  deriving DecidableEq

def Matrix.identity : Matrix := ⟨1, 0, 0, 1⟩

def Matrix.step (s : DivState) (m : Matrix) : Matrix :=
  if s.g % 2 = 0 then ⟨2 * m.u, 2 * m.v, m.q, m.r⟩
  else if 0 < s.delta then ⟨2 * m.q, 2 * m.r, m.q - m.u, m.r - m.v⟩
  else ⟨2 * m.u, 2 * m.v, m.q + m.u, m.r + m.v⟩

def Matrix.Bounded (m : Matrix) (bound : Nat) : Prop :=
  m.u.natAbs + m.v.natAbs ≤ bound ∧ m.q.natAbs + m.r.natAbs ≤ bound

def Matrix.Represents (m : Matrix) (factor : Int) (f g : Int) (s : DivState) : Prop :=
  m.u * f + m.v * g = factor * s.f ∧ m.q * f + m.r * g = factor * s.g

structure JumpState where
  state : DivState
  matrix : Matrix
  deriving DecidableEq

def jump : Nat → JumpState → JumpState
  | 0, s => s
  | n + 1, s => jump n ⟨divstep s.state, s.matrix.step s.state⟩

theorem jump_state (n : Nat) (s : JumpState) :
    (jump n s).state = divsteps n s.state := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _

theorem Matrix.identity_bounded : Matrix.identity.Bounded 1 := by
  change 1 + 0 ≤ 1 ∧ 0 + 1 ≤ (1 : Nat)
  decide +kernel

theorem Matrix.step_bounded (s : DivState) {m : Matrix} {bound : Nat}
    (h : m.Bounded bound) : (m.step s).Bounded (2 * bound) := by
  rcases h with ⟨hfirst, hsecond⟩
  have htwo : (2 : Int).natAbs = 2 := rfl
  dsimp only [Matrix.step]
  split
  · simp only [Matrix.Bounded, Int.natAbs_mul, htwo]
    omega
  · split
    · simp only [Matrix.Bounded, Int.natAbs_mul, htwo]
      have hu := Int.natAbs_sub_le m.q m.u
      have hv := Int.natAbs_sub_le m.r m.v
      omega
    · simp only [Matrix.Bounded, Int.natAbs_mul, htwo]
      have hu := Int.natAbs_add_le m.q m.u
      have hv := Int.natAbs_add_le m.r m.v
      omega

theorem jump_bounded (n : Nat) (s : JumpState) {bound : Nat}
    (h : s.matrix.Bounded bound) : (jump n s).matrix.Bounded (2^n * bound) := by
  induction n generalizing s bound with
  | zero => simpa only [jump, Nat.pow_zero, Nat.one_mul] using h
  | succ n ih =>
    have hnext := ih ⟨divstep s.state, s.matrix.step s.state⟩ (Matrix.step_bounded s.state h)
    simpa only [jump, Nat.pow_succ, Nat.mul_assoc] using hnext

theorem jump_identity_bounded (n : Nat) (s : DivState) :
    (jump n ⟨s, Matrix.identity⟩).matrix.Bounded (2^n) := by
  simpa only [Nat.mul_one] using jump_bounded n ⟨s, Matrix.identity⟩ Matrix.identity_bounded

theorem Matrix.identity_represents (s : DivState) :
    Matrix.identity.Represents 1 s.f s.g s := by
  simp [Matrix.Represents, Matrix.identity]

theorem Matrix.step_represents {s : DivState} {m : Matrix} {factor f g : Int}
    (odd : s.f % 2 = 1) (h : m.Represents factor f g s) :
    (m.step s).Represents (2 * factor) f g (divstep s) := by
  rcases h with ⟨hfirst, hsecond⟩
  dsimp only [Matrix.Represents, Matrix.step, divstep]
  split
  · rename_i heven
    have hhalf : 2 * (s.g / 2) = s.g := by omega
    constructor <;> grind
  · rename_i hodd
    split
    · have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f := by omega
      constructor <;> grind
    · have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f := by omega
      constructor <;> grind

theorem jump_represents (n : Nat) (s : JumpState) {factor f g : Int}
    (odd : s.state.f % 2 = 1) (h : s.matrix.Represents factor f g s.state) :
    (jump n s).matrix.Represents ((2 : Int)^n * factor) f g (jump n s).state := by
  induction n generalizing s factor with
  | zero => simpa only [jump, Int.pow_zero, Int.one_mul] using h
  | succ n ih =>
    have hnext := ih ⟨divstep s.state, s.matrix.step s.state⟩ (divstep_odd odd)
      (Matrix.step_represents odd h)
    simpa only [jump, Int.pow_succ, Int.mul_assoc] using hnext

theorem jump_identity_represents (n : Nat) (s : DivState) (odd : s.f % 2 = 1) :
    (jump n ⟨s, Matrix.identity⟩).matrix.Represents ((2 : Int)^n) s.f s.g
      (divsteps n s) := by
  have h := jump_represents n ⟨s, Matrix.identity⟩ odd (Matrix.identity_represents s)
  simpa only [Int.mul_one, jump_state] using h

theorem linearCombination_natAbs_le {f g u v : Int} {limit bound : Nat}
    (hf : f.natAbs ≤ limit) (hg : g.natAbs ≤ limit)
    (huv : u.natAbs + v.natAbs ≤ bound) :
    (u * f + v * g).natAbs ≤ bound * limit := by
  calc
    (u * f + v * g).natAbs ≤ (u * f).natAbs + (v * g).natAbs :=
      Int.natAbs_add_le _ _
    _ = u.natAbs * f.natAbs + v.natAbs * g.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ u.natAbs * limit + v.natAbs * limit :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hf) (Nat.mul_le_mul_left _ hg)
    _ = (u.natAbs + v.natAbs) * limit := (Nat.add_mul _ _ _).symm
    _ ≤ bound * limit := Nat.mul_le_mul_right _ huv

end P256.Proofs.Field.Inverse.SafeGcd
