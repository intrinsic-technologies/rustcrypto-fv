import P256.Proofs.Field.Representation
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Blocks

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scalarModulus : Limbs := ⟨0xf3b9cac2fc632551, 0xbce6faada7179e84, 0xffffffffffffffff, 0xffffffff00000000⟩

theorem scalar_modulus : scalarModulus.toNat = P256.Spec.Operations.domain.n := by decide +kernel

theorem modulus_limbs {t : RamState} (loaded : ProgramLoaded t)
    (rcx : t.regValue .rcx = 0x2025e0) :
    P256.Proofs.Field.readLimbs t (t.regValue .rcx) = scalarModulus := by
  rw [rcx]
  have h := P256.Proofs.Scalar.Inverse.parameters_modulus loaded
  change Limbs.mk _ _ _ _ = Limbs.mk _ _ _ _
  congr 1
  · exact h.memLoad_limb 0 (by decide)
  · exact h.memLoad_limb 1 (by decide)
  · exact h.memLoad_limb 2 (by decide)
  · exact h.memLoad_limb 3 (by decide)

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
