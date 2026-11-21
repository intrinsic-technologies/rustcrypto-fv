import P256.Proofs.Field.Inverse.Setup.ParameterMemory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar

set_option exponentiation.threshold 512 in
theorem parameter_values [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (setupComponents s) s t)
    (copied : CopiedParameters s t 8) :
    Nat256At t (stackPtr s-128) P256.Spec.Operations.domain.p ∧
    Nat256At t (stackPtr s-96) (2^512 % P256.Spec.Operations.domain.p) := by
  have allocated {offset : Nat} (bound : offset ≤ 880) (size : 32 ≤ offset+8) :
      ∀ i < 32, (t.external[stackPtr s-BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    exact agrees.grow _ ((stack_sub_readable pre.stack bound size).mem i hi)
  constructor
  · apply nat256At_of_memLoad_limbs (by decide +kernel) (allocated (by decide) (by decide))
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h := copied ⟨3, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+40) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨2, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+48) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨1, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+56) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨0, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+64) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
  · apply nat256At_of_memLoad_limbs (by decide +kernel) (allocated (by decide) (by decide))
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h := copied ⟨4, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+72) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨5, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+80) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨6, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+88) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h
    · have h := copied ⟨7, by decide⟩ (by decide)
      change memLoad t.external (stackPtr s-168+96) 64 = _ at h
      simpa [parameterValue, BitVec.sub_eq_add_neg, BitVec.add_assoc] using h

end P256.Proofs.Field.Inverse
