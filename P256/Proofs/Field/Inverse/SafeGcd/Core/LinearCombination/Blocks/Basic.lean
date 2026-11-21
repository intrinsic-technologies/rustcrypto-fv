import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Basic
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Arithmetic
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

theorem sbb_low (c : Bool) (a b : BitVec 64) :
    (Common.Instructions.Carry.sbbSpec a b (BitVec.ofBool c)).1 =
      a - (b + BitVec.ofNat 64 c.toNat) := by
  rw [Common.Instructions.Carry.sbbSpec_result]
  cases c <;> simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

theorem sbb_cf (c : Bool) (a b : BitVec 64) :
    (Common.Instructions.Carry.sbbSpec a b (BitVec.ofBool c)).2.CF =
      (sbbSpec c a b).2.CF := by
  simp only [Common.Instructions.Carry.sbbSpec_cf, BitVec.toNat_ofBool, sbbSpec]

theorem neg_cf (x : BitVec 64) : (negSpec x).2.CF = decide (x ≠ 0) := rfl


theorem adcSpec_low (c : Bool) (x y : BitVec 64) :
    (adcSpec c x y).1 = x + y + BitVec.ofNat 64 c.toNat := rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
