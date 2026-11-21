import X86Proofs.Instructions.Add.Operation

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Counter

open X86 X86.Helpers X86Proofs
open scoped X86.Runtime.Syntax

def addCarryOperation {σ : Type} (x y : BitVec 64) (carry : BitVec 1) :
    Runtime.SpecM Exception (X86.State σ) (BitVec 64) := do
  let (result, carry_out, overflow, alternative_carry) ← X86.Helpers.Add (size := 64) x y carry
  RFLAGS.setOF overflow
  RFLAGS.setSF (← result[64 - 1 +: 1])
  RFLAGS.setZF (← Bit (← Std.Bits.Is_Zero (size := 64) result))
  RFLAGS.setAF alternative_carry
  RFLAGS.setPF (← Bit (← Std.Bits.Is_Parity_Even (size := 8) (← result[0 +: 8])))
  RFLAGS.setCF carry_out
  return result

theorem add_eq_addCarryOperation {σ : Type} (x y : BitVec 64) :
    Instructions.Operations.ADD 64 x y = addCarryOperation (σ := σ) x y 0 := by
  rfl

theorem adc_eq_addCarryOperation {σ : Type} (x y : BitVec 64) :
    Instructions.Operations.ADC 64 x y =
      (do let c ← RFLAGS.CF; addCarryOperation (σ := σ) x y c) := by
  unfold Instructions.Operations.ADC
  simp only [Int.reduceBEq, Bool.false_or, Bool.or_true, assert_of_true, pure_bind]
  rfl

theorem add_zero_carry (x : BitVec 64) (c : Bool) :
    X86.Helpers.Add (size := 64) x 0 (BitVec.ofBool c) =
      X86.Helpers.Add (size := 64) x (BitVec.ofNat 64 c.toNat) 0 := by
  cases c <;> simp [X86.Helpers.Add, x86_runtime]

theorem addCarryOperation_zero {σ : Type} (x : BitVec 64) (c : Bool) :
    addCarryOperation (σ := σ) x 0 (BitVec.ofBool c) =
      addCarryOperation x (BitVec.ofNat 64 c.toNat) 0 := by
  unfold addCarryOperation
  rw [add_zero_carry]

theorem adc_zero_operation {σ : Type} (s : X86.State σ) (x : BitVec 64) :
    (X86.Instructions.Operations.ADC 64 x 0).run s =
      let out := addSpec x (BitVec.ofNat 64 (s.RFLAGS.getLsbD 0).toNat)
      (.ok out.1, setFlags s out.2) := by
  rw [adc_eq_addCarryOperation]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := BitVec.ofBool (s.RFLAGS.getLsbD 0)) ?_).trans ?_
  · change (Except.ok (s.RFLAGS.extractLsb' 0 1), s) = _
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst this
    simp
  · rw [addCarryOperation_zero, ← add_eq_addCarryOperation]
    exact add_operation s 64 (by simp) x _

end Sha2.Proofs.Wrapper512.Absorb.Large.Counter
