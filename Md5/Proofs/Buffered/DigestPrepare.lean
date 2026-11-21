import Md5.Proofs.Buffered.DigestPrepare.Initialize
import Md5.Proofs.Buffered.DigestPrepare.Long
import Md5.Proofs.Buffered.DigestPrepare.Short.Run

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem digest_prepare [bindings : Bindings] {initial : RamState} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      DigestPrepared initial (returnBoundary initial) input s := by
  obtain ⟨n, s, hInit, hs⟩ := DigestPrepare.initialize hReady hCode hCall
  by_cases hShort : input.size < 64
  · obtain ⟨m, t, hRun, ht⟩ := DigestPrepare.prepare_short hStride hCall hs hShort
    exact ⟨n + m, t, hInit.trans hRun, ht⟩
  · have hLong : 64 ≤ input.size := by omega
    obtain ⟨m, t, hRun, ht⟩ := DigestPrepare.prepare_long hStride hCall hs hLong
    exact ⟨n + m, t, hInit.trans hRun, ht⟩

end Md5.Proofs.Buffered
