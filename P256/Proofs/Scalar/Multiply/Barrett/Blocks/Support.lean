import P256.Proofs.Scalar.Multiply.Barrett.Basic

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

theorem byte_extend (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  exact BitVec.setWidth_setWidth (by decide)

theorem add_low {n : Nat} (x y : BitVec n) : (addSpec x y).1 = x + y := rfl

end P256.Proofs.Scalar.Multiply.Barrett
