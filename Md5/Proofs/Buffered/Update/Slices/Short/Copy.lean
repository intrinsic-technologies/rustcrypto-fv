import Md5.Proofs.Buffered.Update.Slices.Short
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.Stack

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem short_copy [Bindings] {variant : Bool} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (he : ((shortReadyEffect variant) s).Holds s u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hshort : input.size < 64 - message.size % 64) :
    ∃ v, MemcpySiteResult boundary (pc variant 0x100327) u v := by
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by simp [shortReadyEffect, Effect.components])
  have hsi : rsi.read u = (Operand.reg (kind variant).inputRegister : Operand 64).read s +
      BitVec.ofNat 64 0 := by
    rw [kind_inputRegister]
    change (Operand.reg 6 : Operand 64).read u = (Operand.reg 14 : Operand 64).read s + 0
    exact he.writes.2.2.2.1.trans (BitVec.add_zero _).symm
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 input.size :=
    he.writes.2.2.2.2.trans (by simpa only [kind_sizeRegister] using h.inputSize)
  have hdi : rdi.read u = (kind variant).context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.1, position_eq h, kind_context]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + 192 =
      stackPtr s + 192 + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hpre : MemcpySitePre (pc variant 0x100327) u := h.memcpySitePre he.agrees hsp hdi hsi hdx
    (by omega) (by omega) (by cases variant <;> decide) (Or.inl (by cases variant <;> decide))
    (by simp [shortReadyEffect, Effect.components])
  have htarget : callMemPtr (pc variant 0x100321) (.rip (if variant then 0xfe729 else 0xffcd9)) u = 0x1024b0 := by
    cases variant <;> exact memcpy_pointer hc
  have hcall : Stack.CallMemPre (pc variant 0x100321) (.rip (if variant then 0xfe729 else 0xffcd9)) u := by
    refine ⟨⟨⟨he.rip, ?_⟩, ?_⟩, (by cases variant <;> exact memcpy_pointer_readable hc)⟩
    · have hw := h.callSlotWritable_of_agrees he.agrees
      simpa only [pushAddr, hsp] using hw
    · rw [htarget]
      decide
  have hbytes : CodeIn (codeRange (pc variant 0x100321) (if variant then [0xff, 0x15, 0x29, 0xe7, 0x0f, 0x00] else [0xff, 0x15, 0xd9, 0xfc, 0x0f, 0x00])) u := by
    cases variant with
    | false => exact program_text_slice hc 0x321 6 (by decide +kernel)
    | true => exact program_text_slice hc 0x18d1 6 (by decide +kernel)
  exact memcpy_call h.stride
    (outside_text_range_of_not_inProgram h.boundaryOutside 0x1024b0 0x1024df
      (by decide) (by cases variant <;> decide +kernel))
    (by cases variant <;> exact Stack.call_m64_rip_effect_step _ _) hr hc hbytes hcall hpre htarget
    (by
      cases variant with
      | false => exact text_address_ne_return h.boundaryOutside 0x327 (by decide +kernel)
      | true => exact text_address_ne_return h.boundaryOutside 0x18d7 (by decide +kernel))

end Md5.Proofs.Buffered.Update.Slices
