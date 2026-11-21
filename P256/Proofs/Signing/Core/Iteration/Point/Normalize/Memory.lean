import P256.Proofs.Signing.Core.Iteration.Point.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs P256.Proofs.Program
open NextNonce (base_add)

theorem bytes_from_stack {s t u : RamState} {output lenOut : Nat}
    (outputBound : output ≤ 2280)
    (bytes : ∀ offset len, offset ≤ 2280 → len ≤ offset+8 →
      (offset+lenOut ≤ 2280-output ∨ 2280-output+len ≤ offset) →
      ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) :
    ∀ offset len, offset+len ≤ 2280 → (offset+len ≤ output ∨ output+lenOut ≤ offset) →
      ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro offset len bound apart i hi
  rw [base_add s (by omega)]
  exact bytes (2280-offset) len (by omega) (by omega) (by omega) i hi

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
