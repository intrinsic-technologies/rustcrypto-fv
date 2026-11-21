import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Step
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Bounds
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Coefficients

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd

def modulus (p : Inputs) : Nat := packFour (p.modulus.map BitVec.toNat)

def argument (p : Inputs) : Nat := packFour (p.a.map BitVec.toNat)

def scale (p : Inputs) : Nat := packFour (p.scale.map BitVec.toNat)

def initialDivState (p : Inputs) : DivState := ⟨1, modulus p, argument p⟩

structure Conditions (p : Inputs) : Prop where
  positive : 0 < modulus p
  odd : (modulus p : Int) % 2 = 1
  coprime : Nat.Coprime 2 (modulus p)
  inverse : ((modulus p : Int) * p.inverse.toNat) % (2 : Int)^64 = 1
  argument_lt : argument p < modulus p
  scale_lt : scale p < modulus p

structure Invariant (p : Inputs) (rounds : Nat) (s : LoopState) : Prop where
  rounds_le : rounds ≤ 591
  remaining : s.remaining = 591 - rounds
  fValid : Valid s.f
  gValid : Valid s.g
  dValid : Valid s.d
  eValid : Valid s.e
  state_eq : state s = divsteps rounds (initialDivState p)
  dBound : magnitude s.d < modulus p
  eBound : magnitude s.e < modulus p
  dRelation : (value s.d * argument p) % modulus p = (value s.f * scale p) % modulus p
  eRelation : (value s.e * argument p) % modulus p = (value s.g * scale p) % modulus p

theorem initial_invariant (p : Inputs) (h : Conditions p) : Invariant p 0 (initialState p) := by
  refine ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_, h.scale_lt, ?_, ?_⟩
  · simpa [magnitude, initialState, packFour] using h.positive
  · have hd : value (initialState p).d = 0 := by
      simp [value, negative, initialState, LinearCombination.inputValue, packFour]
    rw [hd]
    change (0 * (argument p : Int)) % modulus p = ((modulus p : Int) * scale p) % modulus p
    simp
  · change ((scale p : Int) * argument p) % modulus p = ((argument p : Int) * scale p) % modulus p
    rw [Int.mul_comm]

theorem Invariant.fg_bounds {p : Inputs} {rounds : Nat} {s : LoopState}
    (h : Invariant p rounds s) (hc : Conditions p) :
    magnitude s.f ≤ modulus p ∧ magnitude s.g ≤ modulus p := by
  have hb := divsteps_natAbs_le (s := initialDivState p) (limit := modulus p) rounds
    (by simp [initialDivState]) (by simpa only [initialDivState, Int.natAbs_natCast] using
      (Nat.le_of_lt hc.argument_lt))
  rw [← h.state_eq] at hb
  simpa only [state, value_natAbs] using hb

theorem Invariant.delta_bound {p : Inputs} {rounds : Nat} {s : LoopState}
    (h : Invariant p rounds s) : s.delta.toInt.natAbs + 2 * batchCount s ≤ 1183 := by
  have hd := Machine.divsteps_delta_natAbs_le rounds (initialDivState p)
  rw [← h.state_eq] at hd
  change s.delta.toInt.natAbs ≤ 1 + 2 * rounds at hd
  have hc : batchCount s ≤ 591 - rounds := by
    unfold batchCount
    rw [h.remaining]
    exact Nat.min_le_left _ _
  have hr := h.rounds_le
  omega

theorem next_invariant (p : Inputs) (rounds : Nat) (s : LoopState)
    (hc : Conditions p) (h : Invariant p rounds s) :
    Invariant p (rounds + batchCount s) (nextState p s) := by
  have hcount : batchCount s ≤ 62 := Nat.min_le_right _ _
  have hremaining : batchCount s ≤ 591 - rounds := by
    unfold batchCount
    rw [h.remaining]
    exact Nat.min_le_left _ _
  have hodd : value s.f % 2 = 1 := by
    have ho := divsteps_odd (s := initialDivState p) rounds hc.odd
    change (divsteps rounds (initialDivState p)).f % 2 = 1 at ho
    rw [← h.state_eq] at ho
    exact ho
  have hbounds := h.fg_bounds hc
  have hfg := next_fg p s h.fValid h.gValid h.delta_bound hodd hbounds.1 hbounds.2
  have hmatrix := Batch.matrix_represents (batchCount s) (batchInput s) (state s)
    h.delta_bound hcount (batch_low s h.fValid h.gValid) (batch_matrix_identity s) hodd
  have hdb : (value s.d * (batchResult s).u.toInt +
      value s.e * (batchResult s).v.toInt).natAbs < 2^batchCount s * modulus p := by
    have ht := linearCombination_natAbs_lt (f := value s.d) (g := value s.e)
      (limit := modulus p)
      (by simpa only [value_natAbs] using h.dBound)
      (by simpa only [value_natAbs] using h.eBound) hmatrix.2.1
      (Nat.two_pow_pos (batchCount s))
    simpa only [state, Batch.matrix, batchResult, Int.mul_comm] using ht
  have heb : (value s.d * (batchResult s).q.toInt +
      value s.e * (batchResult s).r.toInt).natAbs < 2^batchCount s * modulus p := by
    have ht := linearCombination_natAbs_lt (f := value s.d) (g := value s.e)
      (limit := modulus p)
      (by simpa only [value_natAbs] using h.dBound)
      (by simpa only [value_natAbs] using h.eBound) hmatrix.2.2
      (Nat.two_pow_pos (batchCount s))
    simpa only [state, Batch.matrix, batchResult, Int.mul_comm] using ht
  have hd := modular_step p s.d s.e (batchResult s).u (batchResult s).v (batchCount s)
    h.dValid h.eValid hcount hc.positive hc.inverse hdb
  have he := modular_step p s.d s.e (batchResult s).q (batchResult s).r (batchCount s)
    h.dValid h.eValid hcount hc.positive hc.inverse heb
  change Valid (nextState p s).d ∧ magnitude (nextState p s).d < modulus p ∧
    ((2 : Int)^batchCount s * value (nextState p s).d) % modulus p =
      (value s.d * (batchResult s).u.toInt + value s.e * (batchResult s).v.toInt) % modulus p at hd
  change Valid (nextState p s).e ∧ magnitude (nextState p s).e < modulus p ∧
    ((2 : Int)^batchCount s * value (nextState p s).e) % modulus p =
      (value s.d * (batchResult s).q.toInt + value s.e * (batchResult s).r.toInt) % modulus p at he
  have hrep := hmatrix.1
  rw [← hfg.2.2] at hrep
  change (batchResult s).u.toInt * value s.f + (batchResult s).v.toInt * value s.g =
      (2 : Int)^batchCount s * value (nextState p s).f ∧
    (batchResult s).q.toInt * value s.f + (batchResult s).r.toInt * value s.g =
      (2 : Int)^batchCount s * value (nextState p s).g at hrep
  refine ⟨by have hr := h.rounds_le; omega, ?_, hfg.1, hfg.2.1, hd.1, he.1,
    ?_, hd.2.1, he.2.1, ?_, ?_⟩
  · change s.remaining - batchCount s = 591 - (rounds + batchCount s)
    rw [h.remaining, Nat.sub_sub]
  · rw [hfg.2.2, h.state_eq, divsteps_add]
  · exact P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Coefficients.coefficient_update hc.positive hc.coprime (batchCount s)
      h.dRelation h.eRelation hrep.1.symm (by simpa only [Int.mul_comm] using hd.2.2)
  · exact P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Coefficients.coefficient_update hc.positive hc.coprime (batchCount s)
      h.dRelation h.eRelation hrep.2.symm (by simpa only [Int.mul_comm] using he.2.2)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
