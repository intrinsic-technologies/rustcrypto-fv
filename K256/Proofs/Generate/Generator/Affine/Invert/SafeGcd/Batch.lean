import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.MatrixWords

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Batch

structure Words where
  delta : BitVec 64
  f : BitVec 64
  g : BitVec 64
  u : BitVec 64
  v : BitVec 64
  q : BitVec 64
  r : BitVec 64

def even (p : Words) : Bool := p.g.setWidth 8 &&& 1 == 0

def positive (p : Words) : Bool := decide (0 < p.delta.toInt)

def swap (p : Words) : Bool := !even p && positive p

def numerator (p : Words) : BitVec 64 :=
  if even p then p.g else if positive p then p.g - p.f else p.g + p.f

def next (p : Words) : Words where
  delta := if swap p then 2 - p.delta else p.delta + 2
  f := if swap p then p.g else p.f
  g := (numerator p).sshiftRight 1
  u := if swap p then p.q + p.q else p.u + p.u
  v := if swap p then p.r + p.r else p.v + p.v
  q := if even p then p.q else if positive p then p.q - p.u else p.q + p.u
  r := if even p then p.r else if positive p then p.r - p.v else p.r + p.v

def run : Nat → Words → Words
  | 0, p => p
  | n+1, p => run n (next p)

def state (p : Words) : DivState := ⟨p.delta.toInt, p.f.toInt, p.g.toInt⟩

def matrix (p : Words) : Matrix := ⟨p.u.toInt, p.v.toInt, p.q.toInt, p.r.toInt⟩

def jumpState (p : Words) : JumpState := ⟨state p, matrix p⟩

theorem even_eq (p : Words) : even p = decide (p.g.toInt % 2 = 0) := by
  have h : p.g.setWidth 8 &&& 1#8 =
      if p.g.toInt % 2 = 0 then 0#8 else 1#8 := parity_byte p.g
  change (p.g.setWidth 8 &&& 1#8 == 0#8) = _
  rw [h]
  split <;> simp_all

set_option linter.unusedSimpArgs false in
theorem next_state (p : Words) (bound : p.delta.toInt.natAbs ≤ 1183) :
    state (next p) = wordDivstep (state p) := by
  have h := divstep_values_word p.delta p.f p.g bound
  by_cases he : p.g.toInt % 2 = 0 <;> by_cases hp : 0 < p.delta.toInt <;>
    simpa [state, next, swap, numerator, even_eq, positive, he, hp] using h.symm

set_option linter.unusedSimpArgs false in
theorem next_matrix (p : Words) (bound : (Matrix.step (state p) (matrix p)).Bounded (2^62)) :
    matrix (next p) = Matrix.step (state p) (matrix p) := by
  have h := matrix_step_words (state p) p.u p.v p.q p.r bound
  by_cases he : p.g.toInt % 2 = 0 <;> by_cases hp : 0 < p.delta.toInt <;>
    simpa [state, matrix, next, swap, numerator, even_eq, positive, he, hp] using h.symm

theorem next_jumpState (p : Words) (delta : p.delta.toInt.natAbs ≤ 1183)
    (bound : (Matrix.step (state p) (matrix p)).Bounded (2^62)) :
    jumpState (next p) = ⟨wordDivstep (state p), Matrix.step (state p) (matrix p)⟩ := by
  rw [jumpState, next_state p delta, next_matrix p bound]

theorem run_correct (count used : Nat) (p : Words)
    (delta : p.delta.toInt.natAbs + 2 * count ≤ 1183)
    (bound : (matrix p).Bounded (2^used)) (limit : used + count ≤ 62) :
    jumpState (run count p) = wordJump count (jumpState p) := by
  induction count generalizing used p with
  | zero => rfl
  | succ count ih =>
    have hn : (Matrix.step (state p) (matrix p)).Bounded (2^(used+1)) := by
      simpa only [Nat.pow_succ, Nat.mul_comm] using Matrix.step_bounded (state p) bound
    have hpow : 2^(used+1) ≤ (2:Nat)^62 := Nat.pow_le_pow_right (by decide) (by omega)
    have hn62 : (Matrix.step (state p) (matrix p)).Bounded (2^62) :=
      ⟨Nat.le_trans hn.1 hpow, Nat.le_trans hn.2 hpow⟩
    have hstate := next_state p (by omega)
    have hdelta := wordDivstep_delta_bound (state p)
    rw [← hstate] at hdelta
    change (next p).delta.toInt.natAbs ≤ p.delta.toInt.natAbs + 2 at hdelta
    have hb : (matrix (next p)).Bounded (2^(used+1)) := by
      rw [next_matrix p hn62]
      exact hn
    have he := ih (used+1) (next p) (by omega) hb (by omega)
    change jumpState (run count (next p)) = wordJump count
      ⟨wordDivstep (state p), Matrix.step (state p) (matrix p)⟩
    rw [← next_jumpState p (by omega) hn62]
    exact he

theorem matrix_correct (count : Nat) (p : Words) (s : DivState)
    (delta : p.delta.toInt.natAbs + 2 * count ≤ 1183) (limit : count ≤ 62)
    (low : LowBitsEq 63 (state p) s) (identity : matrix p = Matrix.identity) :
    matrix (run count p) = (jump count ⟨s, Matrix.identity⟩).matrix ∧
      (run count p).delta.toInt = (divsteps count s).delta := by
  have hrun := run_correct count 0 p delta
    (by rw [identity]; exact Matrix.identity_bounded) (by omega)
  have h := wordJump_lowBits (count := count) (bits := 1)
    (left := jumpState p) (right := ⟨s, Matrix.identity⟩)
    (by omega) (low.mono (by omega)) identity
  rw [← hrun] at h
  exact ⟨h.2, by simpa only [jumpState, state, jump_state] using h.1.1⟩

theorem matrix_represents (count : Nat) (p : Words) (s : DivState)
    (delta : p.delta.toInt.natAbs + 2 * count ≤ 1183) (limit : count ≤ 62)
    (low : LowBitsEq 63 (state p) s) (identity : matrix p = Matrix.identity)
    (odd : s.f % 2 = 1) :
    (matrix (run count p)).Represents ((2:Int)^count) s.f s.g (divsteps count s) ∧
      (matrix (run count p)).Bounded (2^count) := by
  rw [(matrix_correct count p s delta limit low identity).1]
  exact ⟨jump_identity_represents count s odd, jump_identity_bounded count s⟩

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Batch
