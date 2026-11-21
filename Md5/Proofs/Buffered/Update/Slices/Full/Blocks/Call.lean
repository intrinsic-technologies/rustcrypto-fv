import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Compression

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem compress_full_input {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {buffer : Standards.RFC.MD5.Buffer} {s u : RamState}
    (h : UpdatePre (kind variant) boundary message input s)
    (ha : AgreesExcept ((kind variant).changes s) s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x1003d8))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hdi : u.regValue .rdi = (kind variant).context s + 64) (offset : Nat)
    (hoffset : offset ≤ input.size)
    (hsi : u.regValue .rsi = (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 offset)
    (hdx : u.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64))
    (hb : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (pc variant 0x1003dd) buffer
      (fullBytes (input.extract offset input.size)) u t := by
  cases variant with
  | false =>
    have hp := h.compressionPre_fullInput ha hsp hdi offset hoffset hsi hdx hb
    have hbytes : CodeIn (codeRange 0x1003d8 (encodeCallRel32 0x17c3)) u :=
      program_text_slice hcode 0x3d8 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Md5.Proofs.Buffered.Stack.call_rel32_effect_step 0x1003d8 0x17c3 (by decide +kernel))
      hready hcode hbytes ⟨hrip, hp.pushWritable⟩ hp rfl
      (by decide +kernel) (by unfold OutsideCompression; decide +kernel) h.boundaryOutside
      (text_address_ne_return h.boundaryOutside 0x3dd (by decide +kernel))
  | true =>
    have hp := h.compressionPre_fullInput ha hsp hdi offset hoffset hsi hdx hb
    have hbytes : CodeIn (codeRange 0x101988 (encodeCallRel32 0x213)) u :=
      program_text_slice hcode 0x1988 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Md5.Proofs.Buffered.Stack.call_rel32_effect_step 0x101988 0x213 (by decide +kernel))
      hready hcode hbytes ⟨hrip, hp.pushWritable⟩ hp rfl
      (by decide +kernel) (by unfold OutsideCompression; decide +kernel) h.boundaryOutside
      (text_address_ne_return h.boundaryOutside 0x198d (by decide +kernel))

end Md5.Proofs.Buffered.Update.Slices
