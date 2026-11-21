import Md5.Proofs.Buffered.Finalize.Digest.Long.Frame

namespace Md5.Proofs.Buffered.Finalize.Digest.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_call [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s u : RamState} (hs : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hdi : s.regValue .rdi = stackPtr s + 8)
    (hPosition : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hBlocks : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64))
    (hCall : FinalizeReset.CompressCall.Post boundary 0x1001a0
      (absorbedBuffer message) (firstBlock message) s u) :
    ∃ t, Post boundary message s t := by
  have hsu := hs.of_agrees hCall.agrees hCall.rsp
  obtain ⟨n, t, ha, hr, hc, he⟩ :=
    Clear.run hCall.ready hCall.code hsu hOutside hCall.rip
  have hsp := (Clear.effect_rsp he).trans hCall.rsp
  have hca := compression_agrees hdi hCall.agrees
  have hcl := clear_agrees he
  have heq : changes u = changes s := by simp only [changes, hCall.rsp]
  rw [heq] at hcl
  have hag : AgreesExcept (changes s) s t := (hca.trans hcl).mono (by simp)
  have hbu : (⟨(stackPtr u + 8).toNat, 16⟩ : MemoryRegion).HasBytes u.external
      ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (firstBlock message))).toBytes.toArray⟩ := by
    simpa only [Compress.outputRegion, registerRegion, hdi, hCall.rsp] using hCall.output
  obtain ⟨m, hm⟩ := hCall.advances
  refine ⟨t, ⟨⟨m + n, hm.trans ha⟩, hr, hc, he.rip,
    hsu.of_agrees he.agrees (Clear.effect_rsp he), hsp, ?_, Clear.effect_buffer he hbu,
    ?_, ?_, agrees_digest hag⟩⟩
  · rw [Clear.effect_rsp he]
    exact Clear.effect_bytes hsu he
  · exact (hag.read (n := 64) (r := 12) (by simp [changes])).trans hPosition
  · exact (hag.read (n := 64) (r := 15) (by simp [changes])).trans hBlocks

end Md5.Proofs.Buffered.Finalize.Digest.Long
