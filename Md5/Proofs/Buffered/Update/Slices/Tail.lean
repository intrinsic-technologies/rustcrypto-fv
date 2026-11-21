import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Slices.Tail.Frame
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic
import Md5.Proofs.Buffered.Update.Preservation
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.Stack

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem tail {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre (kind variant) boundary message input s)
    (hp : BlocksDone variant boundary input s offset buffer count u) :
    ∃ t, BatchDone variant boundary input s offset buffer count t := by
  have hspu : stackPtr u = stackPtr s := hp.agrees.read (n := 64) (r := 4)
    (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
  have hw : MemoryRoutines.WritableRange u (stackPtr u + 255) 1 := by
    rw [hspu]
    cases variant <;> exact h.contextWritable_of_agrees hp.agrees 63 1 (by decide)
  obtain ⟨fv, v, hav, hrv, hcv, he⟩ := tail_ready (variant := variant) boundary h.boundaryOutside
    hp.ready hp.code (by cases variant <;> exact hp.rip) hw
  have hspv : stackPtr v = stackPtr s :=
    (he.agrees.read (n := 64) (r := 4) (by simp [tailReadyEffect, Effect.components])).trans hspu
  have hagv : AgreesExcept ((kind variant).changes s) s v :=
    (hp.agrees.trans (tailReadyEffect.update_agrees hspu he)).mono (by simp)
  have hsize : input.size - offset < 2^32 := by
    have := inputSize_lt h
    omega
  have hsizeReg : (Operand.reg 5 : Operand 64).read u = BitVec.ofNat 64 (input.size - offset) := by
    cases variant <;> exact hp.size
  have hptr : (Operand.reg 14 : Operand 64).read u =
      (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 offset := by
    simpa only [kind_inputRegister] using hp.pointer
  have hsizeNat : ((Operand.reg 5 : Operand 64).read u).toNat = input.size - offset := by
    rw [hsizeReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfull : (Operand.reg 5 : Operand 64).read u &&& 0x7fffffffffffffc0 =
      BitVec.ofNat 64 ((input.size - offset) / 64 * 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [ResetFirst.fullBlockMask_toNat _ (by rw [hsizeNat]; omega), hsizeNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest : (((Operand.reg 5 : Operand 32).read u &&& 63).setWidth 64) =
      BitVec.ofNat 64 ((input.size - offset) % 64) := by
    apply BitVec.eq_of_toNat_eq
    change (((((Operand.reg 5 : Operand 64).read u).setWidth 32) &&& 63).setWidth 64).toNat = _
    rw [ResetFirst.tailMask_toNat, hsizeNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (input.size - offset) % 64 < 2^64 by omega)]
  have hdi : rdi.read v = (kind variant).context s := by
    rw [he.writes.2.2.2.2.2.1, hspu]
    rw [kind_context]
  have hsi : rsi.read v = (Operand.reg 14 : Operand 64).read s +
      BitVec.ofNat 64 (offset + (input.size - offset) / 64 * 64) := by
    rw [he.writes.2.2.2.2.2.2.1, hfull, hptr, BitVec.add_assoc, BitVec.ofNat_add]
  have hdx : MemoryRoutines.rdx.read v = BitVec.ofNat 64 ((input.size - offset) % 64) :=
    he.writes.2.2.2.2.2.2.2.trans hrest
  have hdxn : (MemoryRoutines.rdx.read v).toNat = (input.size - offset) % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpos : (Operand.mem ((kind variant).context s + 63) : Operand 8).read v =
      BitVec.ofNat 8 ((input.size - offset) % 64) := by
    have hv := he.writes.2.2.2.2.1
    change (Operand.mem (stackPtr u + 255) : Operand 8).read v =
      ((((Operand.reg 5 : Operand 32).read u &&& 63).setWidth 64).setWidth 8) at hv
    rw [hrest, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] at hv
    have haddr : stackPtr u + 255 = (kind variant).context s + 63 := by
      rw [hspu]
      rw [kind_context]
      change stackPtr s + 255 = stackPtr s + 192 + 63
      rw [BitVec.add_assoc]
      rfl
    rw [haddr] at hv
    exact hv
  have hpre : MemcpySitePre (pc variant 0x10040f) v := h.memcpySitePre hagv hspv
    (hdi.trans (BitVec.add_zero _).symm) (by simpa only [kind_inputRegister] using hsi) hdx (by omega)
    (by have := hp.offsetBound; omega) (by cases variant <;> decide) (Or.inl (by cases variant <;> decide))
  have htarget : callMemPtr (pc variant 0x100409) (.rip (if variant then 0xfe641 else 0xffbf1)) v = 0x1024b0 := by
    cases variant <;> exact memcpy_pointer hcv
  have hcall : Stack.CallMemPre (pc variant 0x100409) (.rip (if variant then 0xfe641 else 0xffbf1)) v := by
    refine ⟨⟨⟨he.rip, ?_⟩, ?_⟩, (by cases variant <;> exact memcpy_pointer_readable hcv)⟩
    · have hw' := h.callSlotWritable_of_agrees hagv
      simpa only [pushAddr, hspv] using hw'
    · rw [htarget]
      decide
  have hbytes : CodeIn (codeRange (pc variant 0x100409)
      (if variant then [0xff, 0x15, 0x41, 0xe6, 0x0f, 0x00]
       else [0xff, 0x15, 0xf1, 0xfb, 0x0f, 0x00])) v := by
    cases variant with
    | false => exact program_text_slice hcv 0x409 6 (by decide +kernel)
    | true => exact program_text_slice hcv 0x19b9 6 (by decide +kernel)
  obtain ⟨t, hc⟩ := memcpy_call h.stride
    (outside_text_range_of_not_inProgram h.boundaryOutside 0x1024b0 0x1024df
      (by decide) (by decide +kernel))
    (by cases variant <;> exact Stack.call_m64_rip_effect_step _ _) hrv hcv hbytes hcall hpre htarget
    (by
      cases variant with
      | false => exact text_address_ne_return h.boundaryOutside 0x40f (by decide +kernel)
      | true => exact text_address_ne_return h.boundaryOutside 0x19bf (by decide +kernel))
  have hsource : (⟨(rsi.read v).toNat, (tailBytes (input.extract offset input.size)).size⟩ :
      MemoryRegion).HasBytes v.external (tailBytes (input.extract offset input.size)) := by
    have hb := hasBytes_extract (h.inputBytes_of_agrees hagv)
      (offset + (input.size - offset) / 64 * 64) input.size
    have hbound : ((Operand.reg 14 : Operand 64).read s).toNat + input.size < 2^32 := by
      have hi := h.inputBounded
      change ((Operand.reg (kind variant).inputRegister : Operand 64).read s).toNat +
        input.size < 2^32 at hi
      rw [kind_inputRegister] at hi
      exact hi
    have hsin : (rsi.read v).toNat = ((Operand.reg 14 : Operand 64).read s).toNat +
        (offset + (input.size - offset) / 64 * 64) := by
      rw [hsi, toNat_add_ofNat _ _ (by have := hp.offsetBound; omega)]
    rw [tailBytes_extract_suffix input offset hp.offsetBound, hsin]
    simpa only [UpdateKind.inputRegion, kind_inputRegister] using hb
  have htail := hc.hasBytes (by rw [hdxn, size_tailBytes_extract_suffix]) hsource
  rw [hdi] at htail
  have hfcopy := hc.toCallSiteResult.context_prefix_frame h hspv hdi (by rw [hdxn]; omega)
  have hftail : MemoryWriteFrame v t
      #v[UpdateKind.scratchRegion s, ⟨((kind variant).context s).toNat, 64⟩] := by
    intro address hout
    apply hfcopy
    intro region hr hin
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hout (UpdateKind.scratchRegion s) (by simp) hin
    · apply hout ⟨((kind variant).context s).toNat, 64⟩ (by simp)
      have h1 : ((kind variant).context s).toNat ≤ address.toNat := hin.1
      have h2 : address.toNat < ((kind variant).context s).toNat +
        (MemoryRoutines.rdx.read v).toNat := hin.2
      change ((kind variant).context s).toNat ≤ address.toNat ∧
        address.toNat < ((kind variant).context s).toNat + 64
      rw [hdxn] at h2
      omega
  have hstate := h.state_of_tail_frame
    (memoryWriteFrame_trans (tailReadyEffect.frame h hspu he) hftail) hp.bufferBytes
  have hposition := (hc.toCallSiteResult.preserves_position h hspv hdi (by rw [hdxn]; omega)).trans hpos
  have hagcall := hc.toCallSiteResult.update_agrees h hspv
    (hdi.trans (BitVec.add_zero _).symm) (by rw [hdxn]; omega)
  obtain ⟨fu, hau⟩ := hp.advances
  obtain ⟨fc, hac⟩ := hc.advances
  exact ⟨t, ⟨fu + fv + fc, (hau.trans hav).trans hac⟩, hc.ready, hc.code, (by cases variant <;> exact hc.rip),
    (hagv.trans hagcall).mono (by simp), hstate.1, htail, hposition, hstate.2.trans hp.counter⟩

end Md5.Proofs.Buffered.Update.Slices
