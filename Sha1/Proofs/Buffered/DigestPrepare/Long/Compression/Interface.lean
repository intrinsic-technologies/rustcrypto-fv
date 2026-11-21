import Sha1.Proofs.Common.CompressCall
import Sha1.Proofs.Wrapper.Absorb.Mathematics
import Sha1.Proofs.Wrapper.Hash.Serialize

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def compressionChanges (u : RamState) : List Component :=
  Sha1.Proofs.Compress.Routine.frameComponents (stackPtr u - 208) ++
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (u.regValue .rdi) 20,
    .mem (u.regValue .rdi) 4,
    .mem (BitVec.ofNat 64 (Stack.region u Compress.minStackBytes).start)
      (Stack.region u Compress.minStackBytes).size,
    .mem (u.regValue .rdi + 4) 4,
    .mem (u.regValue .rdi + 8) 4,
    .mem (u.regValue .rdi + 12) 4,
    .mem (u.regValue .rdi + 16) 4]

abbrev CompressionCall := Sha1.Proofs.Common.CompressCall.CompressionCall

end Sha1.Proofs.Buffered.DigestPrepare.Long
