import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open Prelude X86 X86.Machine X86.UserProcess

theorem basepoint_correct (bindings : Bindings) : Contract bindings := by
  intro s boundary d pre scalar
  obtain ⟨t, prepared⟩ := table_prepared pre
  exact finish pre prepared scalar

end P256.Proofs.Projective.Multiply.Machine.Basepoint
