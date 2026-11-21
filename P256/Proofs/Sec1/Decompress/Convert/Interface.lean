import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop
    extends CalleePre s boundary 0x108f70 32 32 160 where
  right : s.regValue .rdx = 0x202dc8
  modulus : s.regValue .rcx = 0x202d88
  inverse : s.regValue .r8 = 1

end P256.Proofs.Sec1.Decompress.Convert
