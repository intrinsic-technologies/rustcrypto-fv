import P256.Proofs.Sec1.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def EncodedPointAt (s : RamState) (address : BitVec 64) (bytes : ByteArray) : Prop :=
  EncodingShape bytes ∧ ∀ i < 65, s.external[address + BitVec.ofNat 64 i]? =
    some (bytes.data[i]?.getD 0)

structure AffineDecodePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop extends CalleePre s boundary 0x1100d0 65 80 3360 where
  input : EncodedPointAt s (s.regValue .rsi) bytes

end P256.Proofs.Sec1
