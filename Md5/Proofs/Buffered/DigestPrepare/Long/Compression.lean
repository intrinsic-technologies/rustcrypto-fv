import Md5.Proofs.Buffered.DigestPrepare.Long.Compression.Frame

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compress [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input) (h : Prepared initial input s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Compressed initial input t := by
  have hp := h.compressPre hCall
  obtain ⟨t, ht⟩ := FinalizeReset.CompressCall.run_of_step
    (Buffered.Stack.call_rel32_effect_step 0x1000ae 0x1aed (by decide +kernel))
    h.ready h.code (Block.program_text_slice h.code 0xae 5 (by decide +kernel))
    ⟨h.rip, hp.pushWritable⟩ hp rfl (by decide) (Or.inl (by decide)) h.boundaryOutside
    (Block.text_address_ne_return h.boundaryOutside 0xb3 (by decide +kernel))
  obtain ⟨fuel, hfuel⟩ := ht.advances
  exact ⟨fuel, t, hfuel, h.after_compression hCall ht⟩

end Md5.Proofs.Buffered.DigestPrepare.Long
