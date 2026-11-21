import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Result
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Result
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Result

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open ProjectiveLookup

theorem lookup_correct (bindings : Bindings) : Contract bindings := by
  intro s boundary table digit pre input hdigit
  obtain ⟨n,t,initial,state⟩ := prologue pre hdigit
  obtain ⟨m,u,scanned,state'⟩ := scan pre input state
  exact finish pre hdigit ⟨n+m,initial.trans scanned⟩ state'

end P256.Proofs.Projective.Multiply.Machine.Lookup
