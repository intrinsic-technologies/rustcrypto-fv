import P256.Proofs.Signing.Wrapper.Hash.Frame
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem core_result_frame [Bindings] {initial start entry t : RamState}
    {secret message : ByteArray} (pre : HashEntry initial start secret message)
    (state : Frame initial start entry 528)
    (output : entry.regValue .rdi = stackPtr initial - 456)
    (result : CalleeResult entry t (returnBoundary initial) 65 4584) :
    MemoryWriteFrame entry t #v[workRegion initial] :=
  result.stack_frame (stack pre.context) state.rsp output
    (savedBytes := 240) (by decide) (by decide) (by decide) (by decide)

theorem after_core [Bindings] {initial start entry t : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Frame initial start entry 528)
    (output : entry.regValue .rdi = stackPtr initial - 456)
    (result : CalleeResult entry t (returnBoundary initial) 65 4584) : Frame initial start t :=
  state.after_callee pre.context result output (by decide) (by decide) (by decide) (by decide)

end P256.Proofs.Signing.Wrapper.Hash.Call
