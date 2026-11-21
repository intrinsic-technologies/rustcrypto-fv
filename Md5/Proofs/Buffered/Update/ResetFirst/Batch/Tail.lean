import Md5.Proofs.Buffered.Update.ResetFirst.Batch.Tail.Frame
import Md5.Proofs.Buffered.Update.ResetFirst.Calls
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic
import Md5.Proofs.Buffered.Update.Calls.Frame
import Md5.Proofs.Buffered.Update.ResetFirst.BatchContracts
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem batch_tail_run_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre kind boundary message input s)
    (hu : UpdateBlocksDone kind boundary input s offset buffer count u) :
    ∃ t, UpdateBatchDone kind boundary input s offset buffer count t := by
  have hsp : stackPtr u = stackPtr s := hu.agrees.read (n := 64) (r := 4) (by
    rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  obtain ⟨fv, v, hav, hrv, hcv, he⟩ := tail_ready_of_kind hk h hu.agrees hsp hu.ready hu.code (by rcases hk with rfl | rfl | rfl <;> exact hu.rip)
  have hnum : input.size - offset < 2^32 := by
    have hb : ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
    omega
  have hregsize : (Operand.reg (reg kind 3) : Operand 64).read u =
      BitVec.ofNat 64 (input.size - offset) := by rcases hk with rfl | rfl | rfl <;> exact hu.size
  have hpointer : (Operand.reg kind.inputRegister : Operand 64).read u =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset := hu.pointer
  have hsize : ((Operand.reg (reg kind 3) : Operand 64).read u).toNat = input.size - offset := by
    rw [hregsize, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfull : (Operand.reg (reg kind 3) : Operand 64).read u &&& 0x7fffffffffffffc0 =
      BitVec.ofNat 64 ((input.size - offset) / 64 * 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [ResetFirst.fullBlockMask_toNat _ (by rw [hsize]; omega), hsize,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest : (((Operand.reg (reg kind 3) : Operand 32).read u &&& 63).setWidth 64) =
      BitVec.ofNat 64 ((input.size - offset) % 64) := by
    apply BitVec.eq_of_toNat_eq
    change ((((Operand.reg (reg kind 3) : Operand 64).read u).setWidth 32 &&& 63).setWidth 64).toNat = _
    rw [ResetFirst.tailMask_toNat, hsize, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (input.size - offset) % 64 < 2^64 by omega)]
  have hagv : AgreesExcept (kind.changes s) s v :=
    (hu.agrees.trans (tailReadyEffect.update_agrees_of_kind hk hsp he)).mono (by simp)
  have hvsp : stackPtr v = stackPtr s := hagv.read (n := 64) (r := 4) (by
    rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hdi : rdi.read v = kind.context s := by
    exact he.writes.2.2.2.2.2.1.trans (by rcases hk with rfl | rfl | rfl <;> exact congrArg (fun p : BitVec 64 ↦ p + _) hsp)
  have hsi : rsi.read v = (Operand.reg kind.inputRegister : Operand 64).read s +
      BitVec.ofNat 64 (offset + (input.size - offset) / 64 * 64) := by
    rw [he.writes.2.2.2.2.2.2.1, hfull, hpointer, BitVec.ofNat_add, BitVec.add_assoc]
  have hdx : MemoryRoutines.rdx.read v = BitVec.ofNat 64 ((input.size - offset) % 64) :=
    he.writes.2.2.2.2.2.2.2.trans hrest
  have hdxn : (MemoryRoutines.rdx.read v).toNat = (input.size - offset) % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hslot : Memory.MemWritable v (pushAddr v) 8 := by
    simpa only [pushAddr, hvsp] using h.callSlotWritable_of_agrees hagv
  have hpre : MemcpySitePre (pc kind 0x765 + 6) v := h.memcpySitePre hagv hvsp
    (hdi.trans (BitVec.add_zero _).symm) hsi hdx (by omega) (by have := hu.offsetBound; omega)
    (by rcases hk with rfl | rfl | rfl <;> decide) (by rcases hk with rfl | rfl | rfl <;> left <;> decide)
  obtain ⟨t, hc⟩ := memcpy_rip_of_kind hk h.stride (.inr (.inr rfl)) h.boundaryOutside hrv hcv he.rip
    hslot hpre
  have hcopyFrame := hc.toCallSiteResult.context_prefix_frame h hvsp hdi (by rw [hdxn]; omega)
  have hf : MemoryWriteFrame u t #v[UpdateKind.scratchRegion s,
      ⟨(kind.context s).toNat, 64⟩] := by
    apply memoryWriteFrame_trans (tailReadyEffect.frame_of_kind hk h hsp he)
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
    change (Operand.mem (stackPtr u + stackOffset kind 71) : Operand 8).read v =
      ((((Operand.reg (reg kind 3) : Operand 32).read u) &&& 63).setWidth 64).setWidth 8 at hp
    rw [hrest, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] at hp
    have haddr : stackPtr u + stackOffset kind 71 = kind.context s + 63 := by
      rw [hsp]
      rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    simpa only [haddr] using hp
  have hcallag := hc.toCallSiteResult.update_agrees h hvsp
    (hdi.trans (BitVec.add_zero _).symm) (by rw [hdxn]; omega)
  obtain ⟨fu, hau⟩ := hu.advances
  obtain ⟨fc, hac⟩ := hc.advances
  refine ⟨t, ⟨⟨fu + fv + fc, (hau.trans hav).trans hac⟩, hc.ready, hc.code, (by rcases hk with rfl | rfl | rfl <;> exact hc.rip),
    (hagv.trans hcallag).mono (by simp), hb, ?_, ?_, hcounter.trans hu.counter⟩⟩
  · simpa only [hdi] using htail
  · exact (hc.toCallSiteResult.preserves_position h hvsp hdi (by rw [hdxn]; omega)).trans hpos

theorem batch_tail_run [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre .resetFirst boundary message input s)
    (hu : UpdateBlocksDone .resetFirst boundary input s offset buffer count u) :
    ∃ t, BatchDone boundary input s offset buffer count t := by
  exact batch_tail_run_of_kind (kind := .resetFirst) (Or.inl rfl) h hu

end Md5.Proofs.Buffered.ResetFirst
