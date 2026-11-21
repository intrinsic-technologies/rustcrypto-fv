import Md5.Proofs.Buffered.Update.ResetFirst.FillCopy
import Md5.Proofs.Buffered.Update.ResetFirst.FillCompress
import Md5.Proofs.Buffered.Update.ResetFirst.FillFrame
import Md5.Proofs.Buffered.Update.ResetFirst.BatchContracts
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic
import Md5.Proofs.Buffered.Update.Fill.Copy
import Md5.Proofs.Buffered.Update.Preservation.Compression

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem filled_ready_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ t, UpdateBatchReady kind boundary input s (64 - message.size % 64)
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))) (message.size / 64 + 1) t := by
  have hcap : 64 - message.size % 64 ≤ input.size := by omega
  have hsize : input.size < 2^64 := by have := h.totalSize; omega
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := fill_ready_of_kind hk h hfull hpos
  obtain ⟨v, hv⟩ := fill_copy_of_kind hk h he hru hcu hfull
  have hspu : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
    rcases hk with rfl | rfl | rfl <;>
      simp [fillReadyEffect_of_kind, Effect.components, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister])
  have hspv : stackPtr v = stackPtr s := hv.rsp.trans hspu
  have hdiu : rdi.read u = kind.context s +
      BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.2.2.1, position_of_pre_of_kind h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + stackOffset kind 8 =
      stackPtr s + stackOffset kind 8 + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hsiu : rsi.read u = (.reg kind.inputRegister : Operand 64).read s := he.writes.2.2.2.2.2
  have hdxu : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64) :=
    he.writes.2.1.trans (capacity_of_pre_of_kind h)
  have hextu : u.external = s.external := he.agrees.external (by
    simp [fillReadyEffect_of_kind, Effect.components, Component.Covers])
  obtain ⟨hbv, hbufv, hcounterv⟩ := filledBlock_of_copy h hv hextu hspu hdiu hsiu hdxu hcap
  obtain ⟨fw, w, z, haw, hi, hz⟩ :=
    fill_compress_of_kind hk h (he.agrees.trans hv.agrees) hspv hv.ready hv.code hv.rip hcap hbv hbufv
  have hspw : stackPtr w = stackPtr s :=
    (hi.agrees.read (n := 64) (r := 4) (by simp [incrementPrepareEffect_of_kind, Effect.components])).trans hspv
  have hspz : stackPtr z = stackPtr s := hz.rsp.trans hspw
  have hdiw : w.regValue .rdi = kind.context s + 64 := by
    change (.reg 7 : Operand 64).read w = _
    rw [hi.writes.2.2.1, hspv]
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
  have hcountBound : message.size % 64 + (MemoryRoutines.rdx.read u).toNat ≤ 88 := by
    rw [hdxu, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 64 - message.size % 64 < 2^64 by omega)]
    omega
  have hagv : AgreesExcept (kind.changes s) s v := by
    exact ((fillReadyEffect_agrees_of_kind hk he).trans
      (hv.toCallSiteResult.update_agrees h hspu hdiu hcountBound)).mono (by simp)
  have hagw : AgreesExcept (kind.changes s) s w :=
    (hagv.trans (incrementPrepareEffect_agrees_of_kind hk hspv hi)).mono (by simp)
  have hagz : AgreesExcept (kind.changes s) s z :=
    (hagw.trans (hz.update_agrees h hspw hdiw)).mono (by simp)
  have haddr : stackPtr v + stackOffset kind 88 = kind.context s + 80 := by
    rw [hspv]
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
  have hcounterw : (.mem (kind.context s + 80) : Operand 64).read w =
      BitVec.ofNat 64 (message.size / 64 + 1) := by
    have hh := hi.writes.1
    change (.mem (stackPtr v + stackOffset kind 88) : Operand 64).read w =
      (.mem (stackPtr v + stackOffset kind 88) : Operand 64).read v + 1 at hh
    rw [haddr, hcounterv] at hh
    rw [BitVec.ofNat_add]
    exact hh
  have hcounterz := (hz.update_counter h hspw hdiw).trans hcounterw
  have hbufferz : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      z.external ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))).toBytes.toArray⟩ := by
    simpa only [h.compressionOutputRegion hdiw] using hz.output
  have hzPointer : (.reg kind.sizeRegister : Operand 64).read z =
      (.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64) := by
    rw [hz.agrees.read (n := 64) (r := kind.sizeRegister) (by rcases hk with rfl | rfl | rfl <;> simp [FinalizeReset.CompressCall.changes, UpdateKind.sizeRegister]),
      hi.agrees.read (n := 64) (r := kind.sizeRegister) (by rcases hk with rfl | rfl | rfl <;> simp [incrementPrepareEffect_of_kind, Effect.components, UpdateKind.sizeRegister]),
      hv.agrees.read (n := 64) (r := kind.sizeRegister) (by rcases hk with rfl | rfl | rfl <;> simp [callSiteChanges, UpdateKind.sizeRegister]),
      he.writes.2.2.2.1, capacity_of_pre_of_kind h]
  have hzRemainder : (.reg (reg kind 3) : Operand 64).read z =
      BitVec.ofNat 64 (input.size - (64 - message.size % 64)) := by
    rw [hz.agrees.read (n := 64) (r := reg kind 3) (by rcases hk with rfl | rfl | rfl <;> simp [FinalizeReset.CompressCall.changes, reg]),
      hi.agrees.read (n := 64) (r := reg kind 3) (by rcases hk with rfl | rfl | rfl <;> simp [incrementPrepareEffect_of_kind, Effect.components, reg]),
      hv.agrees.read (n := 64) (r := reg kind 3) (by rcases hk with rfl | rfl | rfl <;> simp [callSiteChanges, reg]),
      he.writes.2.2.1]
    change (.reg kind.sizeRegister : Operand 64).read s - (64 - position_of_kind kind s) = _
    have hs : (.reg kind.sizeRegister : Operand 64).read s = BitVec.ofNat 64 input.size := h.inputSize
    rw [hs, capacity_of_pre_of_kind h]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hcap
  have hshift : (.reg (reg kind 3) : Operand 64).read z >>> 6 =
      BitVec.ofNat 64 ((input.size - (64 - message.size % 64)) / 64) := by
    rw [hzRemainder, ofNat_ushiftRight 64 _ 6 (by omega)]
  have hwpos : MemoryRoutines.WritableRange z (stackPtr z + stackOffset kind 71) 1 := by
    rw [hspz]
    have hw := h.contextWritable_of_agrees hagz 63 1 (by decide)
    rcases hk with rfl | rfl | rfl <;> simpa [stackOffset, UpdateKind.contextOffset] using hw
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ := fill_count_of_kind hk boundary h.boundaryOutside
    hz.ready hz.code hz.rip hwpos
  obtain ⟨hbt, hctail⟩ := h.state_of_tail_frame (fillCountEffect_frame_of_kind hk h hspz hf) hbufferz
  obtain ⟨fv, hav⟩ := hv.advances
  obtain ⟨fz, haz⟩ := hz.advances
  refine ⟨t, ⟨⟨fu + fv + fw + fz + ft, (((hau.trans hav).trans haw).trans haz).trans hat⟩,
    hrt, hct, ?_, ?_, hcap, ?_, ?_, ?_, hbt, hctail.trans hcounterz⟩⟩
  · rw [hf.rip]
    change (if (.reg (reg kind 3) : Operand 64).read z >>> 6 = 0 then _ else _) = _
    rw [hshift]
    have heq : BitVec.ofNat 64 ((input.size - (64 - message.size % 64)) / 64) = 0 ↔
        (input.size - (64 - message.size % 64)) / 64 = 0 := by
      constructor
      · intro heq
        have hh := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show (input.size - (64 - message.size % 64)) / 64 < 2^64 by omega)] at hh
        exact hh
      · intro heq
        rw [heq]
        rfl
    simp only [heq]
    rcases hk with rfl | rfl | rfl <;> rfl
  · exact (hagz.trans (fillCountEffect_agrees_of_kind hk hspz hf)).mono (by simp)
  · exact hf.writes.2.1.trans hzPointer
  · have hreg : kind.batchSizeRegister = reg kind 3 := by
      rcases hk with rfl | rfl | rfl <;> rfl
    rw [hreg]
    exact (hf.agrees.read (n := 64) (r := reg kind 3)
      (by rcases hk with rfl | rfl | rfl <;> simp [fillCountEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister])).trans hzRemainder
  · exact hf.writes.2.2.trans hshift


theorem filled_ready [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ t, BatchReady boundary input s (64 - message.size % 64)
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))) (message.size / 64 + 1) t := by
  exact filled_ready_of_kind (kind := .resetFirst) (Or.inl rfl) h hfull hpos

end Md5.Proofs.Buffered.ResetFirst
