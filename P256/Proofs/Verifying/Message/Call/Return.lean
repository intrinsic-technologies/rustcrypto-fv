import P256.Proofs.Verifying.Message.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Call

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem core_result_frame [Bindings] {initial t : RamState}
    (result : Core.Frame initial t) :
    MemoryWriteFrame initial t #v[registerRegion initial .rdi 24, Stack.region initial 9992] :=
  result.frame

theorem after_core [Bindings] {initial t : RamState}
    (result : Core.Frame initial t) : Message.Frame initial t :=
  { result with frame := core_result_frame result }

end P256.Proofs.Verifying.Message.Call
