import Hkdf.Proofs.Common.State

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix

open Prelude X86 X86.Machine Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

structure RekeyedAt (s : RamState) (p : BitVec 64) (key : ByteArray) : Prop where
  innerHash : HashStateAt s p
    (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x36))
  innerBlocks : loadBytes s.external (p + 32) 8 = .ok 1
  outerHash : HashStateAt s (p + 40)
    (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c))
  outerBlocks : loadBytes s.external (p + 72) 8 = .ok 1

end Hkdf.Proofs.Standard.Finalize.Suffix
