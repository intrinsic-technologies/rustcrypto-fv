import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Compression
import Md5.Proofs.Buffered.Update.Fill.Copy
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.Stack

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem fill_copy_call {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {changes : List Component}
    (h : UpdatePre (kind variant) boundary message input s) (ha : AgreesExcept changes s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x100389))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hdi : rdi.read u = (kind variant).context s + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read u = (Operand.reg 14 : Operand 64).read s)
    (hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64))
    (hfull : 64 - message.size % 64 ≤ input.size) (hd : Component.df ∉ changes) :
    ∃ t, MemcpySiteResult boundary (pc variant 0x10038f) u t := by
  cases variant with
  | false =>
    have hp : MemcpySitePre 0x10038f u := h.memcpySitePre ha hsp hdi
      (hsi.trans (BitVec.add_zero _).symm) hdx (by omega) (by omega)
      (by decide) (Or.inl (by decide)) hd
    have htarget : callMemPtr 0x100389 (.rip 0xffc71) u = 0x1024b0 :=
      memcpy_pointer hcode
    have hslot : Memory.MemWritable u (pushAddr u) 8 := by
      simpa only [pushAddr, hsp] using h.callSlotWritable_of_agrees ha
    have hbytes : CodeIn (codeRange 0x100389 [0xff, 0x15, 0x71, 0xfc, 0x0f, 0x00]) u :=
      program_text_slice hcode 0x389 6 (by decide +kernel)
    exact memcpy_call h.stride
      (outside_text_range_of_not_inProgram h.boundaryOutside 0x1024b0 0x1024df
        (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x100389 0xffc71) hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return h.boundaryOutside 0x38f (by decide +kernel))
  | true =>
    have hp : MemcpySitePre 0x10193f u := h.memcpySitePre ha hsp hdi
      (hsi.trans (BitVec.add_zero _).symm) hdx (by omega) (by omega)
      (by decide) (Or.inl (by decide)) hd
    have htarget : callMemPtr 0x101939 (.rip 0xfe6c1) u = 0x1024b0 :=
      memcpy_pointer hcode
    have hslot : Memory.MemWritable u (pushAddr u) 8 := by
      simpa only [pushAddr, hsp] using h.callSlotWritable_of_agrees ha
    have hbytes : CodeIn (codeRange 0x101939 [0xff, 0x15, 0xc1, 0xe6, 0x0f, 0x00]) u :=
      program_text_slice hcode 0x1939 6 (by decide +kernel)
    exact memcpy_call h.stride
      (outside_text_range_of_not_inProgram h.boundaryOutside 0x1024b0 0x1024df
        (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x101939 0xfe6c1) hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return h.boundaryOutside 0x193f (by decide +kernel))

theorem compress_filled_context {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {changes : List Component}
    (h : UpdatePre (kind variant) boundary message input s) (ha : AgreesExcept changes s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x1003ac))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hdi : u.regValue .rdi = (kind variant).context s + 64)
    (hsi : u.regValue .rsi = (kind variant).context s)
    (hdx : u.regValue .rdx = 1)
    (hfull : 64 - message.size % 64 ≤ input.size)
    (hi : (⟨((kind variant).context s).toNat, 64⟩ : MemoryRegion).HasBytes
      u.external (updateBlock message input))
    (hb : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨(absorbedBuffer message).toBytes.toArray⟩) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (pc variant 0x1003b1)
      (absorbedBuffer message) (updateBlock message input) u t := by
  cases variant with
  | false =>
    have hp := h.compressionPre_context ha hsp hdi hsi hdx
      (size_updateBlock message input hfull) hi hb
    have hbytes : CodeIn (codeRange 0x1003ac (encodeCallRel32 0x17ef)) u :=
      program_text_slice hcode 0x3ac 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x1003ac 0x17ef (by decide +kernel))
      hready hcode hbytes ⟨hrip, hp.pushWritable⟩ hp rfl
      (by decide +kernel) (by unfold OutsideCompression; decide +kernel) h.boundaryOutside
      (text_address_ne_return h.boundaryOutside 0x3b1 (by decide +kernel))
  | true =>
    have hp := h.compressionPre_context ha hsp hdi hsi hdx
      (size_updateBlock message input hfull) hi hb
    have hbytes : CodeIn (codeRange 0x10195c (encodeCallRel32 0x23f)) u :=
      program_text_slice hcode 0x195c 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x10195c 0x23f (by decide +kernel))
      hready hcode hbytes ⟨hrip, hp.pushWritable⟩ hp rfl
      (by decide +kernel) (by unfold OutsideCompression; decide +kernel) h.boundaryOutside
      (text_address_ne_return h.boundaryOutside 0x1961 (by decide +kernel))

end Md5.Proofs.Buffered.Update.Slices
