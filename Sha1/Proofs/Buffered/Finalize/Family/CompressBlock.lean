import Sha1.Proofs.Buffered.Finalize.Family.CompressArgs
import Sha1.Proofs.Buffered.Finalize.Family.CompressSite
import Sha1.Proofs.Compress.Blocks

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

set_option maxHeartbeats 800000 in
theorem compress_block [bindings : Bindings] {b : ReturnBoundary} {s : RamState}
    {p : BitVec 64} {H : Vector (BitVec 32) 5} {block : ByteArray}
    (stride : UnitStringStride bindings) (outside : ¬ InProgram b.rip)
    (storage : Storage .updateFinalizeCopy s) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programImage s) (df : DirectionFlagClear s.RFLAGS)
    (pc : p = 0x101e9d ∨ p = 0x101f69) (hip : s.RIP = p) (size : block.size = 64)
    (bytes : (⟨(stackPtr s + 128).toNat, 64⟩ : MemoryRegion).HasBytes s.external block)
    (state : StateBytes s H) : ∃ t, SitePost b (p + 23) H block s t := by
  obtain ⟨n, u, hn, hu, hcode, he⟩ := compression_args ready code outside pc hip
  have reg (r : BitVec 5) (hr : r ≠ 7 ∧ r ≠ 6 ∧ r ≠ 2) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read s := by
    apply he.agrees.read
    simp_all [argumentEffect, Effect.components]
  have hsp : stackPtr u = stackPtr s := reg 4 (by decide)
  have ext := he.agrees.external (by simp [argumentEffect, Effect.components, Component.Covers])
  have hw := he.writes
  simp only [argumentEffect, Write.AllHold] at hw
  have run : Run b s u := by
    refine ⟨⟨n, hn⟩, hu, hcode, hsp, ?_, ?_⟩
    · unfold savedOutput
      change memLoad u.external _ 64 = memLoad s.external _ 64
      rw [hsp, ext]
    · apply he.agrees.mono
      intro c hc
      simp [argumentEffect, Effect.components] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp [Kind.changes]
  have site : SitePre b (p + 18) H block u := by
    refine ⟨storage.of_agrees run.agrees hsp, hu, hcode, he.rip, outside, ?_, ?_, ?_,
      hw.2.2, size, ?_, ?_⟩
    · exact (he.agrees.directionFlagClear (by simp [argumentEffect, Effect.components]) ⟨df⟩).df
    · rw [hsp]; exact hw.1
    · rw [hsp]; exact hw.2.1
    · rw [hsp, ext]; exact bytes
    · rw [hsp, ext]; exact state
  have result : ∃ t, SitePost b (p + 23) H block u t := by
    have bridge : Sha1.Proofs.Common.CompressCall.CompressionCall :=
      Sha1.Proofs.Common.CompressCall.compression_call Sha1.Proofs.Compress.block_correct
    rcases pc with h | h <;> rw [h] at site ⊢
    · exact compress_site (disp := 0x62c) (off := 0x1eaf) bridge stride site rfl
        (by decide +kernel) (by decide)
        (program_text_slice hcode 0x1eaf 5 (by decide +kernel)) (by decide)
        (text_address_ne_return outside 0x1eb4 (by decide +kernel))
    · exact compress_site (disp := 0x560) (off := 0x1f7b) bridge stride site rfl
        (by decide +kernel) (by decide)
        (program_text_slice hcode 0x1f7b 5 (by decide +kernel)) (by decide)
        (text_address_ne_return outside 0x1f80 (by decide +kernel))
  obtain ⟨t, ht⟩ := result
  exact ⟨t, run.trans ht.toRun, ht.rip, ht.state,
    ht.r14.trans (reg 14 (by decide)), ht.r15.trans (reg 15 (by decide))⟩

end Sha1.Proofs.Buffered.Finalize.Family
