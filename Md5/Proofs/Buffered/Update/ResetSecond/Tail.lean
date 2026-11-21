import Md5.Proofs.Buffered.Update.ResetSecond.Tail.Frame
import Md5.Proofs.Buffered.Update.ResetSecond.Calls
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic
import Md5.Proofs.Buffered.Update.Calls.Frame
import Md5.Proofs.Buffered.Update.Batch
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail_done [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (hu : UpdateBlocksDone kind boundary input s offset buffer count u) :
    ∃ t, UpdateBatchDone kind boundary input s offset buffer count t := by
  have hsp : stackPtr u = stackPtr s := hu.agrees.read (n := 64) (r := 4) (by
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  obtain ⟨fv, v, hav, hrv, hcv, he⟩ := tail_ready hkind h hu.agrees hsp hu.ready hu.code (by rcases hkind with rfl | rfl | rfl <;> exact hu.rip)
  have hnum : input.size - offset < 2^32 := by
    have hb : ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
    omega
  have hregsize : (Operand.reg 14 : Operand 64).read u =
      BitVec.ofNat 64 (input.size - offset) := by
    rcases hkind with rfl | rfl | rfl <;> exact hu.size
  have hpointer : (Operand.reg kind.inputRegister : Operand 64).read u =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset := hu.pointer
  have hsize : ((Operand.reg 14 : Operand 64).read u).toNat = input.size - offset := by
    rw [hregsize, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfull : (Operand.reg 14 : Operand 64).read u &&& 0x7fffffffffffffc0 =
      BitVec.ofNat 64 ((input.size - offset) / 64 * 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [ResetFirst.fullBlockMask_toNat _ (by rw [hsize]; omega), hsize,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest : (((Operand.reg 14 : Operand 32).read u &&& 63).setWidth 64) =
      BitVec.ofNat 64 ((input.size - offset) % 64) := by
    apply BitVec.eq_of_toNat_eq
    change ((((Operand.reg 14 : Operand 64).read u).setWidth 32 &&& 63).setWidth 64).toNat = _
    rw [ResetFirst.tailMask_toNat, hsize, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (input.size - offset) % 64 < 2^64 by omega)]
  have hagv : AgreesExcept (kind.changes s) s v :=
    (hu.agrees.trans (tailReadyEffect.update_agrees hkind hsp he)).mono (by simp)
  have hvsp : stackPtr v = stackPtr s := hagv.read (n := 64) (r := 4) (by
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hdi : rdi.read v = kind.context s := by
    rcases hkind with rfl | rfl | rfl
    · exact he.writes.2.2.2.2.2.1.trans ((hu.agrees.read (n := 64) (r := 3) (by
        simp [UpdateKind.changes, UpdateKind.workRegisters])).trans (h.secondRegisters (Or.inl rfl)).1)
    · exact he.writes.2.2.2.2.2.1.trans ((hu.agrees.read (n := 64) (r := 3) (by
        simp [UpdateKind.changes, UpdateKind.workRegisters])).trans (h.secondRegisters (Or.inr rfl)).1)
    · simpa only [UpdateKind.context, hsp, ite_true] using he.writes.2.2.2.2.2.1
  have hsi : rsi.read v = (Operand.reg kind.inputRegister : Operand 64).read s +
      BitVec.ofNat 64 (offset + (input.size - offset) / 64 * 64) := by
    have hw : rsi.read v = (Operand.reg kind.inputRegister : Operand 64).read u +
        ((Operand.reg 14 : Operand 64).read u &&& 0x7fffffffffffffc0) := by
      rcases hkind with rfl | rfl | rfl
      · exact he.writes.2.2.2.1
      · exact he.writes.2.2.2.1
      · exact he.writes.2.2.2.2.2.2.2
    rw [hw, hfull, hpointer, BitVec.ofNat_add, BitVec.add_assoc]
  have hdx : MemoryRoutines.rdx.read v = BitVec.ofNat 64 ((input.size - offset) % 64) := by
    rcases hkind with rfl | rfl | rfl
    · exact he.writes.2.2.2.2.2.2.trans hrest
    · exact he.writes.2.2.2.2.2.2.trans hrest
    · exact he.writes.2.2.2.2.2.2.1.trans hrest
  have hdxn : (MemoryRoutines.rdx.read v).toNat = (input.size - offset) % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr15 : (Operand.reg 15 : Operand 64).read v = 0x1024b0 := by
    have hp : (Operand.reg 15 : Operand 64).read v = (Operand.reg 15 : Operand 64).read s :=
      hagv.read (by rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
    rw [hp]
    rcases hkind with rfl | rfl | rfl
    · exact (h.secondRegisters (Or.inl rfl)).2
    · exact (h.secondRegisters (Or.inr rfl)).2
    · exact h.discardSecondMemcpy rfl
  have hslot : Memory.MemWritable v (pushAddr v) 8 := by
    simpa only [pushAddr, hvsp] using h.callSlotWritable_of_agrees hagv
  have hpre : MemcpySitePre (pc kind 0x100a6f) v := h.memcpySitePre hagv hvsp
    (hdi.trans (BitVec.add_zero _).symm) hsi hdx (by omega) (by have := hu.offsetBound; omega)
    (by rcases hkind with rfl | rfl | rfl <;> decide +kernel)
    (by left; rcases hkind with rfl | rfl | rfl <;> decide +kernel)
  obtain ⟨t, hc⟩ := memcpy_r15 h.stride (by rcases hkind with rfl | rfl | rfl <;> simp [tailReadyEffect, pc]) h.boundaryOutside hrv hcv he.rip
    hr15 hslot (by rcases hkind with rfl | rfl | rfl <;> exact hpre)
  have hcopyFrame := hc.toCallSiteResult.context_prefix_frame h hvsp hdi (by rw [hdxn]; omega)
  have hf : MemoryWriteFrame u t #v[UpdateKind.scratchRegion s,
      ⟨(kind.context s).toNat, 64⟩] := by
    apply memoryWriteFrame_trans (tailReadyEffect.frame h hsp he)
    intro address hout
    apply hcopyFrame
    intro region hr hh
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hout _ (by simp) hh
    · apply hout ⟨(kind.context s).toNat, 64⟩ (by simp)
      change (kind.context s).toNat ≤ _ ∧
        _ < (kind.context s).toNat + 64
      have hh' := hh.2
      change _ < (kind.context s).toNat + (MemoryRoutines.rdx.read v).toNat at hh'
      rw [hdxn] at hh'
      exact ⟨hh.1, by omega⟩
  obtain ⟨hb, hcounter⟩ := h.state_of_tail_frame hf hu.bufferBytes
  have htailInput : (⟨(rsi.read v).toNat,
      (tailBytes (input.extract offset input.size)).size⟩ : MemoryRegion).HasBytes
      v.external (tailBytes (input.extract offset input.size)) := by
    have hi := hasBytes_extract (h.inputBytes_of_agrees hagv)
      (offset + (input.size - offset) / 64 * 64) input.size
    rw [tailBytes_extract_suffix input offset hu.offsetBound]
    have hn : (rsi.read v).toNat = ((Operand.reg kind.inputRegister : Operand 64).read s).toNat +
        (offset + (input.size - offset) / 64 * 64) := by
      rw [hsi]
      apply toNat_add_ofNat
      have hb : ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
      have := hu.offsetBound
      omega
    rw [hn]
    exact hi
  have htail := hc.hasBytes (by rw [hdxn, size_tailBytes_extract_suffix]) htailInput
  have hpos : (Operand.mem (kind.context s + 63) : Operand 8).read v =
      BitVec.ofNat 8 ((input.size - offset) % 64) := by
    have hp := he.writes.2.2.2.2.1
    change (Operand.mem (kind.context u + 63) : Operand 8).read v =
      ((((Operand.reg 14 : Operand 32).read u) &&& 63).setWidth 64).setWidth 8 at hp
    rw [hrest, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] at hp
    have haddr : kind.context u + 63 = kind.context s + 63 := by
      simp only [UpdateKind.context, hsp]
    simpa only [haddr] using hp
  have hcallag := hc.toCallSiteResult.update_agrees h hvsp
    (hdi.trans (BitVec.add_zero _).symm) (by rw [hdxn]; omega)
  obtain ⟨fu, hau⟩ := hu.advances
  obtain ⟨fc, hac⟩ := hc.advances
  refine ⟨t, ⟨⟨fu + fv + fc, (hau.trans hav).trans hac⟩, hc.ready, hc.code, (by rcases hkind with rfl | rfl | rfl <;> exact hc.rip),
    (hagv.trans hcallag).mono (by simp), hb, ?_, ?_, hcounter.trans hu.counter⟩⟩
  · simpa only [hdi] using htail
  · exact (hc.toCallSiteResult.preserves_position h hvsp hdi (by rw [hdxn]; omega)).trans hpos

end Md5.Proofs.Buffered.ResetSecond
