import P256.Proofs.Program.Code
import P256.Proofs.Scalar.Inverse.Interface

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem parameters_modulus {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x2025e0 P256.Spec.Operations.domain.n := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x2025e0 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (P256.Spec.Operations.domain.n / 256 ^ i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

theorem parameters_adjuster {s : RamState} (loaded : ProgramLoaded s) :
    Nat256At s 0x2025c0 (1) := by
  refine ⟨by decide +kernel, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x2025c0 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat ((1) / 256 ^ i.val % 256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i, hi⟩)

end P256.Proofs.Scalar.Inverse
