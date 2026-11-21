import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) (odd : Bool) : Prop extends CalleePre s boundary 0x10fc00 32 80 2592 where
  input : (registerRegion s .rsi 32).HasBytes s.external bytes
  size : bytes.size = 32
  parity : s.regValue .rdx = BitVec.ofNat 64 odd.toNat

end P256.Proofs.Sec1.Decompress
