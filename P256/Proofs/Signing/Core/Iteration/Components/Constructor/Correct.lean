import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

theorem correct : Components.ConstructorContract := by
  intro bindings s boundary r scalarS pre first second firstBound secondBound
  obtain ⟨t, state⟩ := decode pre first second firstBound secondBound
  exact finish pre.toCalleePre state

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
