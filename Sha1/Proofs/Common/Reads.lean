import Sha1.Proofs.Common.Output

namespace Sha1.Proofs.Common

open Prelude X86 X86.Machine Sha1.Spec Sha1.Spec.Program

 theorem digest_readOutput_of_hasBytes {initial final : RamState} {digest : Vector UInt8 20}
    (h : (Digest.outputRegion initial).HasBytes final.external ⟨digest.toArray⟩) :
    Digest.readOutput initial final = .ok digest := by
  exact readBytes_of_hasBytes (initial := initial) h

 theorem compress_readOutput_of_hasBytes {initial final : RamState} {digest : Vector UInt8 20}
    (h : (Compress.outputRegion initial).HasBytes final.external ⟨digest.toArray⟩) :
    Compress.readOutput initial final = .ok digest := by
  exact readBytes_of_hasBytes (initial := initial) h

end Sha1.Proofs.Common
