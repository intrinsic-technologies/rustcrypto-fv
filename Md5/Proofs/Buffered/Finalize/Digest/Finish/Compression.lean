import Md5.Proofs.Buffered.Finalize.Compression
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace Compression

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {message : ByteArray}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hs : Storage .digest s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = 0x10025b)
    (hdi : s.regValue .rdi = stackPtr s + 8)
    (hsi : s.regValue .rsi = stackPtr s + 112)
    (hdx : s.regValue .rdx = 1)
    (hi : (⟨(stackPtr s + 112).toNat, 64⟩ : MemoryRegion).HasBytes
      s.external (lastBlock message))
    (hb : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    ∃ t, FinalizeReset.CompressCall.Post boundary 0x100260 buffer (lastBlock message) s t := by
  have h112 : (stackPtr s + 112).toNat = (stackPtr s).toNat + 112 :=
    hs.stackAddress (offset := 112) (by decide)
  have h8 : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 :=
    hs.stackAddress (offset := 8) (by decide)
  have hp : FinalizeReset.CompressCall.Pre buffer (lastBlock message) s :=
    hs.compressCallPre (src := 112) (dst := 8) hsi hdi
    (by rw [hdx, size_lastBlock]; rfl)
    (by rw [size_lastBlock]; decide) (by decide) (Or.inr (by decide))
    (by rw [size_lastBlock]; rwa [h112] at hi)
    (by rwa [h8] at hb)
  exact FinalizeReset.CompressCall.run_of_step
    (Buffered.Stack.call_rel32_effect_step 0x10025b 0x1940 (by decide +kernel)) hr hc
    (Block.program_text_slice hc 0x25b 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
    (by decide +kernel) (by decide) (Or.inl (by decide)) hout
    (Block.text_address_ne_return hout 0x260 (by decide +kernel))

theorem agrees {s t : RamState} (hdi : s.regValue .rdi = stackPtr s + 8)
    (h : AgreesExcept (FinalizeReset.CompressCall.changes s) s t) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Kind.changes, Kind.workRegisters, Kind.localChanges, Component.isMem]
  · intro a c hc ha
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨i, by omega, rfl⟩
    · exact ⟨.mem (stackPtr s - 320) 320, by simp [Kind.changes], ha⟩

end Compression

end Md5.Proofs.Buffered.Finalize.Digest.Finish
