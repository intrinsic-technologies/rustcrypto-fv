import X86Proofs.Instructions.Add.Operation
import X86Proofs.Instructions.Sub.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Carry

open X86 X86.Helpers X86Proofs

def adcSpec {n : Nat} (x y : BitVec n) (c : BitVec 1) : BitVec n × StatusFlags :=
  let u : Int := x.toNat + y.toNat + c.toNat
  let r := BitVec.ofInt n u
  (r, { OF := decide (r.toInt ≠ x.toInt + y.toInt + c.toNat),
        CF := decide ((r.toNat : Int) ≠ u),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide (((BitVec.ofInt 4 u).toNat : Int) ≠
          (x.extractLsb' 0 4).toNat + (y.extractLsb' 0 4).toNat + c.toNat) })

def sbbSpec {n : Nat} (x y : BitVec n) (c : BitVec 1) : BitVec n × StatusFlags :=
  let u : Int := x.toNat - (y.toNat + c.toNat)
  let r := BitVec.ofInt n u
  (r, { OF := decide (r.toInt ≠ x.toInt - (y.toInt + c.toNat)),
        CF := decide ((r.toNat : Int) ≠ u),
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := decide (((BitVec.ofInt 4 u).toNat : Int) ≠
          (x.extractLsb' 0 4).toNat - ((y.extractLsb' 0 4).toNat + c.toNat)) })

theorem adcSpec_result {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (adcSpec x y c).1 = x + y + c.setWidth n := by
  simp [adcSpec, BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem sbbSpec_result {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (sbbSpec x y c).1 = x - y - c.setWidth n := by
  simp only [sbbSpec, Int.sub_eq_add_neg, Int.neg_add, BitVec.ofInt_add,
    BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem add_with_carry {n : Nat} (hn : 4 ≤ n) (x y : BitVec n) (c : BitVec 1) :
    Add (size := n) x y c = .ok
      ((adcSpec x y c).1, BitVec.ofBool (adcSpec x y c).2.CF,
        BitVec.ofBool (adcSpec x y c).2.OF, BitVec.ofBool (adcSpec x y c).2.AF) := by
  simp only [X86.Helpers.Add, Int.natCast_nonneg, decide_true, assert_of_true,
    Runtime.CheckedSlice.read, Runtime.intSlice, Int.toNat_natCast, Std.le_refl,
    Bool.and_self, Runtime.Unsigned, Int.toNat_one, Int.toNat_zero, Int.pow_zero,
    Int.ediv_one, bind_pure_comp, map_pure, Int.reduceSub, Int.reduceAdd,
    Runtime.sliceInclusive, Int.zero_le_ofNat, Int.zero_add, show (4 : Int) ≤ n by omega,
    slice_eq_pure, Int.reduceToNat, Int.sub_zero, beq_iff_eq, BitVec.ofNat_eq_ofNat,
    Runtime.Signed, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.reducePow,
    Int.natCast_emod, Int.cast_ofNat_Int, adcSpec, ne_eq, decide_not]
  rw [ite_zero_one, ite_zero_one, ite_zero_one]
  rfl

theorem subtract_with_borrow {n : Nat} (hn : 4 ≤ n) (x y : BitVec n) (c : BitVec 1) :
    Subtract (size := n) x y c = .ok
      ((sbbSpec x y c).1, BitVec.ofBool (sbbSpec x y c).2.CF,
        BitVec.ofBool (sbbSpec x y c).2.OF, BitVec.ofBool (sbbSpec x y c).2.AF) := by
  simp only [X86.Helpers.Subtract, Int.natCast_nonneg, decide_true, assert_of_true,
    Runtime.CheckedSlice.read, Runtime.intSlice, Int.toNat_natCast, Std.le_refl,
    Bool.and_self, Runtime.Unsigned, Int.toNat_one, Int.toNat_zero, Int.pow_zero,
    Int.ediv_one, bind_pure_comp, map_pure, Int.reduceSub, Int.reduceAdd,
    Runtime.sliceInclusive, Int.zero_le_ofNat, Int.zero_add, show (4 : Int) ≤ n by omega,
    slice_eq_pure, Int.reduceToNat, Int.sub_zero, beq_iff_eq, BitVec.ofNat_eq_ofNat,
    Runtime.Signed, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.reducePow,
    Int.natCast_emod, Int.cast_ofNat_Int, sbbSpec, ne_eq, decide_not]
  rw [ite_zero_one, ite_zero_one, ite_zero_one]
  rfl

theorem readCF_run {σ : Type} (s : State σ) :
    RFLAGS.CF.run s = (.ok (s.RFLAGS.extractLsb' 0 1), s) := by rfl

theorem adc_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.ADC n x y).run s =
      let (r, flags) := adcSpec x y (s.RFLAGS.extractLsb' 0 1)
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.ADC
    spec_bind_rfl
    spec_bind_with readCF_run s
    simp (disch := decide) only [add_with_carry, isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, adcSpec, Int.reduceToNat, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, Nat.pow_one, Int.natCast_emod, ne_eq, decide_not,
      BitVec.extractLsb'_eq_self, Nat.reducePow, BitVec.ofNat_eq_ofNat, beq_zero_eq_decide,
      Int.reduceSub, Int.toNat_one, Nat.reduceAdd, extractLsb'_msb, decide_eq_true_eq,
      Int.toNat_zero, specM_pure_run, setFlags, StatusFlags.store]
    repeat rw [ite_one_zero]
    simp only [Bool.decide_eq_true]

theorem sbb_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    (X86.Instructions.Operations.SBB n x y).run s =
      let (r, flags) := sbbSpec x y (s.RFLAGS.extractLsb' 0 1)
      (.ok r, setFlags s flags) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SBB
    spec_bind_rfl
    spec_bind_with readCF_run s
    simp (disch := decide) only [subtract_with_borrow, isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, sbbSpec, Int.reduceToNat, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, Nat.pow_one, Int.natCast_emod, ne_eq, decide_not,
      BitVec.extractLsb'_eq_self, Nat.reducePow, BitVec.ofNat_eq_ofNat, beq_zero_eq_decide,
      Int.reduceSub, Int.toNat_one, Nat.reduceAdd, extractLsb'_msb, decide_eq_true_eq,
      Int.toNat_zero, specM_pure_run, setFlags, StatusFlags.store]
    repeat rw [ite_one_zero]
    simp only [Bool.decide_eq_true]

end P256.Proofs.Common.Instructions.Carry
