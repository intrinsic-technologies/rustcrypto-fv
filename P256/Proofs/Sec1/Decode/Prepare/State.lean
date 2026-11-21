import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Sec1.EncodedPoint

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BufferReady [Bindings] (initial s : RamState) (bytes : ByteArray) : Prop
    extends Frame initial s where
  rip : s.RIP = 0x10e561
  destination : s.regValue .r15 = initial.regValue .rdi
  zero : s.regValue .r12 = 0
  encoded : EncodedPointAt s (stackPtr initial - 312) bytes

end P256.Proofs.Sec1.Decode.Prepare
