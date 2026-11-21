import Md5.Proofs.Buffered.DigestPrepare.Long.Preparation
import Md5.Proofs.Buffered.DigestPrepare.Long.Compression
import Md5.Proofs.Buffered.DigestPrepare.Long.Tail

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_long [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hLong : 64 ≤ input.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  obtain ⟨n, u, ha, hu⟩ := Long.prepare_compression hCall h hLong
  obtain ⟨m, v, hb, hv⟩ := Long.compress hCall hu
  obtain ⟨k, t, hc, ht⟩ := Long.finish_compressed hStride hCall hv
  exact ⟨n + m + k, t, (ha.trans hb).trans hc, ht⟩

end Md5.Proofs.Buffered.DigestPrepare
