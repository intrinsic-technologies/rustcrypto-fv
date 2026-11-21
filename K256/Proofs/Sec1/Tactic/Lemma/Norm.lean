import K256.Proofs.Common.Refine.LayoutAttr
import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Common.Lift.Reg
import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace K256.Proofs.Refine

open X86Proofs K256.Proofs.Lift

private theorem bmod_cases (d : Int) (N : Nat) (h1 : -(2 * (N : Int)) < d) (h2 : d < 2 * N) :
    d.bmod (2 * N) = if d < -N then d + 2 * N else if N ≤ d then d - 2 * N else d := by
  split
  · rw [← Int.add_bmod_right]
    push_cast
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · split
    · rw [← Int.sub_bmod_right]
      push_cast
      exact Int.bmod_eq_of_le (by omega) (by omega)
    · exact Int.bmod_eq_of_le (by omega) (by omega)

theorem sub_msb_bne_overflow {n : Nat} (x y : BitVec n) :
    ((x - y).msb != decide ((x - y).toInt ≠ x.toInt - y.toInt)) = decide (x.toInt < y.toInt) := by
  rcases n with _ | n
  · simp [BitVec.of_length_zero, BitVec.toInt_zero]
  · have h1 := BitVec.le_two_mul_toInt (x := x)
    have h2 := BitVec.two_mul_toInt_lt (x := x)
    have h3 := BitVec.le_two_mul_toInt (x := y)
    have h4 := BitVec.two_mul_toInt_lt (x := y)
    have hp : (2 : Int) ^ (n + 1) = 2 * ((2 ^ n : Nat) : Int) := by
      push_cast
      rw [Int.pow_succ]
      omega
    have hpn : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, hpn]
    rw [hp] at h1 h2 h3 h4
    have hN : 0 < 2 ^ n := Nat.two_pow_pos n
    generalize 2 ^ n = N at h1 h2 h3 h4 hN ⊢
    rw [bmod_cases _ _ (by omega) (by omega)]
    split
    · rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq]
      omega
    · split
      · rw [Bool.eq_iff_iff]
        simp only [bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq]
        omega
      · rw [Bool.eq_iff_iff]
        simp only [bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq, not_true_eq_false,
          iff_false, Decidable.not_not]
        omega

section Compare

variable {n : Nat} (x y : BitVec n)

theorem subSpec_ZF : (subSpec x y).2.ZF = (x == y) := cmpSpec_ZF x y

@[refine_norm] theorem cmpSpec_CF : (cmpSpec x y).CF = decide (x.toNat < y.toNat) := rfl
@[refine_norm] theorem subSpec_CF : (subSpec x y).2.CF = decide (x.toNat < y.toNat) := rfl

@[refine_norm] theorem cmpSpec_lt :
    ((cmpSpec x y).SF != (cmpSpec x y).OF) = decide (x.toInt < y.toInt) :=
  sub_msb_bne_overflow x y

@[refine_norm] theorem cmpSpec_ge :
    ((cmpSpec x y).SF == (cmpSpec x y).OF) = decide (y.toInt ≤ x.toInt) := by
  have h := cmpSpec_lt x y
  revert h
  cases (cmpSpec x y).SF <;> cases (cmpSpec x y).OF <;> simp <;> omega

@[refine_norm] theorem subSpec_lt :
    ((subSpec x y).2.SF != (subSpec x y).2.OF) = decide (x.toInt < y.toInt) :=
  cmpSpec_lt x y

@[refine_norm] theorem subSpec_ge :
    ((subSpec x y).2.SF == (subSpec x y).2.OF) = decide (y.toInt ≤ x.toInt) :=
  cmpSpec_ge x y

@[refine_norm] theorem beq_or_toInt_lt :
    ((x == y) || decide (x.toInt < y.toInt)) = decide (x.toInt ≤ y.toInt) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
  omega

@[refine_norm] theorem toNat_lt_or_beq :
    (decide (x.toNat < y.toNat) || (x == y)) = decide (x.toNat ≤ y.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
  omega

theorem toInt_eq_biased {n : Nat} (x : BitVec (n + 1)) :
    x.toInt = (((x.toNat + 2 ^ n) % 2 ^ (n + 1) : Nat) : Int) - (2 ^ n : Nat) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hx := x.isLt
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  rw [hp] at hx ⊢
  generalize 2 ^ n = N at hx ⊢
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
    push_cast
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    push_cast
    omega

end Compare

attribute [refine_norm] cmpSpec_ZF subSpec_ZF BitVec.slt_eq_decide BitVec.sle_eq_decide
  BitVec.ult_eq_decide BitVec.ule_eq_decide

section Logic

variable {n : Nat} (x : BitVec n)

@[refine_norm] theorem testFlags_ZF : (testFlags x).ZF.getD false = (x == 0) := rfl
@[refine_norm] theorem testFlags_SF : (testFlags x).SF.getD false = x.msb := rfl
@[refine_norm] theorem testFlags_CF : (testFlags x).CF.getD false = false := rfl
@[refine_norm] theorem testFlags_OF : (testFlags x).OF.getD false = false := rfl

end Logic

attribute [refine_norm] BitVec.and_self Bool.bne_false beq_false

@[refine_norm] theorem setWidth_get {n m : Nat} (v : Value) (h : n ≤ m) :
    (v.get m).setWidth n = v.get n := by
  simp only [Value.get, BitVec.setWidth_setWidth_of_le _ h]

@[refine_norm] theorem setWidth_setWidth_self {n m : Nat} (x : BitVec n) (h : n ≤ m) :
    (x.setWidth m).setWidth n = x := by
  rw [BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

section Low

variable {w k : Nat} (x y : BitVec w)

@[refine_norm] theorem setWidth_sub (h : k ≤ w) :
    (x - y).setWidth k = x.setWidth k - y.setWidth k := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ h,
    BitVec.setWidth_neg_of_le h]

@[refine_norm] theorem setWidth_and_of_le (_ : k ≤ w) :
    (x &&& y).setWidth k = x.setWidth k &&& y.setWidth k := BitVec.setWidth_and

@[refine_norm] theorem setWidth_or_of_le (_ : k ≤ w) :
    (x ||| y).setWidth k = x.setWidth k ||| y.setWidth k := BitVec.setWidth_or

@[refine_norm] theorem setWidth_xor_of_le (_ : k ≤ w) :
    (x ^^^ y).setWidth k = x.setWidth k ^^^ y.setWidth k := BitVec.setWidth_xor

end Low

attribute [refine_norm] BitVec.setWidth_add BitVec.setWidth_mul BitVec.setWidth_not
  BitVec.setWidth_neg_of_le BitVec.setWidth_shiftLeft_of_le

attribute [refine_norm] extractLsb'_memLoad

attribute [refine_norm] Bool.or_eq_true Bool.and_eq_true Bool.or_eq_false_iff
  Bool.and_eq_false_iff decide_eq_true_eq beq_iff_eq bne_iff_ne Bool.not_eq_true'
  decide_eq_false_iff_not ne_eq beq_eq_false_iff_ne

end K256.Proofs.Refine
