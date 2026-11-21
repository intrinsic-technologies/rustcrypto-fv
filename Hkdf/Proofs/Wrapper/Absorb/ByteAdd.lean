import Hkdf.Proofs.Common.Instructions.AddByte.Effect

set_option autoImplicit false

namespace Hkdf.Proofs.Wrapper.Absorb

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Hkdf.Proofs.Common.Instructions.AddByte

theorem mergeGPR8_low (value : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 value old).setWidth 8 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, mergeGPR,
    show ¬ (8 : Nat) = 32 by decide, ite_false]
  rw [getLsbD_setSlice old 0 8 value i (by omega)]
  simp [hi]

end Hkdf.Proofs.Wrapper.Absorb
