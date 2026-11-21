import P256.Proofs.Field.Inverse.SafeGcd.Correction.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

variable {s : RamState} {a m : Nat}

theorem inputs_value (ha : Nat256At s (s.regValue .rsi) a)
    (hm : Nat256At s (s.regValue .rcx) m) (bound : a < m) :
    (limbs (correctedWords (inputs s))).toNat =
      if a = 0 ∨ ((s.regValue .rdx).setWidth 8 ^^^
        memLoad s.external (s.regValue .rsi + 32) 8) &&& 1 = 0 then a else m-a := by
  have ha' : (limbs (inputs s).magnitude).toNat = a := readLimbs_toNat ha
  have hm' : (limbs (inputs s).modulus).toNat = m := readLimbs_toNat hm
  have h := correctedWords_value (inputs s) (by rw [ha', hm']; exact bound)
  rw [ha', hm'] at h
  exact h

end P256.Proofs.Field.Inverse.SafeGcd.Correction
