import Md5.Proofs.Buffered.Finalize.Compression

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Compression

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x10019b) (hSize : input.size = 64)
    (hdi : s.regValue .rdi = stackPtr s + 8)
    (hsi : s.regValue .rsi = stackPtr s + 112)
    (hdx : s.regValue .rdx = 1)
    (hInput : (⟨(stackPtr s + 112).toNat, input.size⟩ : MemoryRegion).HasBytes
      s.external input)
    (hBuffer : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    ∃ t, FinalizeReset.CompressCall.Post boundary 0x1001a0 buffer input s t := by
  have h112 : (stackPtr s + 112).toNat = (stackPtr s).toNat + 112 :=
    hStorage.stackAddress (offset := 112) (by decide)
  have h8 : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 :=
    hStorage.stackAddress (offset := 8) (by decide)
  have hp := hStorage.compressCallPre (buffer := buffer) (src := 112) (dst := 8) hsi hdi
    (by rw [hdx, hSize]; rfl) (by rw [hSize]; decide) (by decide)
    (Or.inr (by decide))
    (by rwa [h112] at hInput)
    (by rwa [h8] at hBuffer)
  exact FinalizeReset.CompressCall.run_of_step
    (Buffered.Stack.call_rel32_effect_step 0x10019b 0x1a00 (by decide +kernel)) hReady hCode
    (Block.program_text_slice hCode 0x19b 5 (by decide +kernel)) ⟨hRip, hp.pushWritable⟩ hp
    (by decide +kernel) (by decide) (Or.inl (by decide)) hOutside
    (Block.text_address_ne_return hOutside 0x1a0 (by decide +kernel))

end Md5.Proofs.Buffered.Finalize.Digest.Long.Compression
