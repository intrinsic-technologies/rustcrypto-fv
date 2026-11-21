import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory
import P256.Proofs.Projective.Constants

set_option autoImplicit false

open P256.Proofs.Program (CalleePre stack_region_end)
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

export Projective.Constants (identity_at identity_byte_inProgram identity_readable)

theorem identity_stack_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) :
    0x202490 + 96 ≤ (stackPtr s - 344#64).toNat ∨
      (stackPtr s - 344#64).toNat + 96 ≤ 0x202490 :=
  Projective.Constants.identity_stack_disjoint pre (by decide) (by decide)

end P256.Proofs.Projective.Multiply.Machine.Lookup
