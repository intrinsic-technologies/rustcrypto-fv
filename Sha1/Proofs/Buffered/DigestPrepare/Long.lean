import Sha1.Proofs.Buffered.DigestPrepare.Long.Preparation
import Sha1.Proofs.Compress.Blocks
import Sha1.Proofs.Buffered.DigestPrepare.Long.Compression
import Sha1.Proofs.Buffered.DigestPrepare.Long.Tail

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_long_of_compression [bindings : Bindings] {initial s : RamState}
    {input : ByteArray} (hBridge : Long.CompressionCall)
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (hp : Initialized initial (returnBoundary initial) input s)
    (hLong : 64 ≤ input.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  obtain ⟨n, u, ha, hu⟩ := Long.prepare_compression hCall hp hLong
  obtain ⟨m, v, hb, hv⟩ := Long.compress hBridge hStride hCall hu
  obtain ⟨k, t, hc, ht⟩ := Long.finish_compressed hStride hCall hv
  exact ⟨n + m + k, t, (ha.trans hb).trans hc, ht⟩

theorem prepare_long [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (hp : Initialized initial (returnBoundary initial) input s)
    (hLong : 64 ≤ input.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  exact prepare_long_of_compression
    (Sha1.Proofs.Common.CompressCall.compression_call
      Sha1.Proofs.Compress.block_correct)
    hStride hCall hp hLong

end Sha1.Proofs.Buffered.DigestPrepare
