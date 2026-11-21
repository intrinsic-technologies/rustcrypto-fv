import Sha2.Proofs.Common.SHA512.Memory
import Sha2.Proofs.Common.Memory.LoadBytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CompressionPre.hashWord [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt64} {input : ByteArray} {count i : Nat}
    (pre : CompressionPre s boundary hash input count) (hi : i < 8) :
    memLoad s.external (s.regValue .rdi + BitVec.ofNat 64 (8 * i)) 64 = hash[i]!.toBitVec :=
  Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64 (pre.hashWords.2 i hi)

end Sha2.Proofs.Common.SHA512
