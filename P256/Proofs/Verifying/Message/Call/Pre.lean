import P256.Proofs.Verifying.Message.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Call

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem core_pre [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Pre initial boundary message) : Core.Pre initial boundary :=
  ⟨pre.toCalleePre, pre.signatureBounded, pre.signatureAllocated, pre.signatureStack⟩

end P256.Proofs.Verifying.Message.Call
