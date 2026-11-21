import Sha1.Proofs.Buffered.DigestPrepare.Initialize
import Sha1.Proofs.Buffered.DigestPrepare.Short
import Sha1.Proofs.Buffered.DigestPrepare.Long

namespace Sha1.Proofs.Buffered

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem digest_prepare [bindings : Bindings] {initial : RamState} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      DigestPrepared initial (returnBoundary initial) input s := by
  obtain ⟨n, s, hInit, hs⟩ := DigestPrepare.«initialize» hReady hCode hCall
  by_cases hShort : input.size < 64
  · obtain ⟨m, t, hRun, ht⟩ := DigestPrepare.prepare_short hStride hCall hs hShort
    exact ⟨n + m, t, hInit.trans hRun, ht⟩
  · have hLong : 64 ≤ input.size := by omega
    obtain ⟨m, t, hRun, ht⟩ := DigestPrepare.prepare_long hStride hCall hs hLong
    exact ⟨n + m, t, hInit.trans hRun, ht⟩

end Sha1.Proofs.Buffered
