import P256.Proofs.HMAC.Mathematics
import P256.Proofs.Program.Interface

set_option autoImplicit false

namespace P256.Proofs.HMAC.Key

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) (key : ByteArray) : Prop
    extends CalleePre s boundary 0x129370 key.size 64 384 where
  short : key.size ≤ 64
  count : s.regValue .rdx = BitVec.ofNat 64 key.size
  input : (registerRegion s .rsi key.size).HasBytes s.external key

end P256.Proofs.HMAC.Key
