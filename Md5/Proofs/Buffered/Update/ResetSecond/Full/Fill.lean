import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Copy
import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Compress
import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Frame
import Md5.Proofs.Buffered.Update.Preservation.Compression
import Md5.Proofs.Buffered.Update.Batch

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem filled_ready [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ t, UpdateBatchReady kind boundary input s (64 - message.size % 64)
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))) (message.size / 64 + 1) t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := fill_ready hkind h hfull hpos
  obtain ⟨v, hc⟩ := fill_copy hkind h he hru hcu hfull
  have husp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by rcases hkind with rfl | rfl | rfl <;> simp [fillReadyEffect, Effect.components, positionRegister, savedInputRegister])
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans husp
  have hdi : rdi.read u = kind.context s +
      BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.2.2.1, position_of_pre h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 kind.contextOffset =
      stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hsi : rsi.read u = (Operand.reg kind.inputRegister : Operand 64).read s :=
    he.writes.2.2.2.2.2
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64) :=
    he.writes.2.1.trans (capacity_of_pre h)
  have hdxn : (MemoryRoutines.rdx.read u).toNat = 64 - message.size % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hext : u.external = s.external := he.agrees.external (by
    simp [fillReadyEffect, Effect.components, Component.Covers])
  obtain ⟨hblock, hbuffer, hcounter⟩ := filledBlock_of_copy h hc hext husp hdi hsi hdx (by omega)
  have hagv : AgreesExcept (kind.changes s) s v :=
    ((fillReadyEffect_agrees hkind he).trans (hc.toCallSiteResult.update_agrees h husp hdi
      (by rw [hdxn]; omega))).mono (by simp)
  have hrbx : kind ≠ .resetDiscardSecond → (Operand.reg 3 : Operand 64).read v = kind.context s := by
    intro hd
    have hk : kind = .resetSecond ∨ kind = .finalizeResetSecond := by rcases hkind with h | h | h; exact Or.inl h; exact Or.inr h; exact (hd h).elim
    exact (hagv.read (n := 64) (r := 3) (by rcases hk with rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])).trans
      (h.secondRegisters hk).1
  obtain ⟨fw, w, x, haw, hi, hx⟩ := fill_compress hkind h hagv hvsp hrbx hc.ready hc.code hc.rip
    (by omega) hblock hbuffer
  have hwsp : stackPtr w = stackPtr s :=
    (hi.agrees.read (n := 64) (r := 4)
      (by rcases hkind with rfl | rfl | rfl <;> simp [incrementPrepareEffect, Effect.components])).trans hvsp
  have hwdi : w.regValue .rdi = kind.context s + 64 := by
    rw [show w.regValue .rdi = (Operand.reg 7 : Operand 64).read w from rfl, hi.writes.2.2.1]
    simp only [UpdateKind.context, hvsp]
  have hagw : AgreesExcept (kind.changes s) s w :=
    (hagv.trans (incrementPrepareEffect_agrees hkind hvsp hi)).mono (by simp)
  have hagx : AgreesExcept (kind.changes s) s x :=
    (hagw.trans (hx.update_agrees h hwsp hwdi)).mono (by simp)
  have hxsp : stackPtr x = stackPtr s := hx.rsp.trans hwsp
  have hwrite : MemoryRoutines.WritableRange x (kind.context x + 63) 1 := by
    simpa [UpdateKind.context, hxsp, BitVec.add_assoc, ← BitVec.ofNat_add] using h.contextWritable_of_agrees hagx 63 1 (by decide)
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ := fill_count hkind boundary h.boundaryOutside
    hx.ready hx.code hx.rip hwrite
  have hxbuffer : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      x.external ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))).toBytes.toArray⟩ := by
    rw [← h.compressionOutputRegion hwdi]
    exact hx.output
  obtain ⟨htbuffer, htcount⟩ := h.state_of_tail_frame (fillCountEffect_frame hkind h hxsp hf) hxbuffer
  have haddr : kind.context v + 80 = kind.context s + 80 := by
    simp only [UpdateKind.context, hvsp]
  have hwcount : (Operand.mem (kind.context s + 80) : Operand 64).read w =
      BitVec.ofNat 64 (message.size / 64 + 1) := by
    have hiwrite := hi.writes.1
    change (Operand.mem (kind.context v + 80) : Operand 64).read w =
      (Operand.mem (kind.context v + 80) : Operand 64).read v + 1 at hiwrite
    rw [haddr, hcounter] at hiwrite
    rw [hiwrite, BitVec.ofNat_add]
    rfl
  have savedInputV : (Operand.reg (savedInputRegister kind) : Operand 64).read v =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64) := by
    rw [hc.agrees.read (n := 64) (r := savedInputRegister kind) (by rcases hkind with rfl | rfl | rfl <;> simp [callSiteChanges, savedInputRegister]),
      he.writes.2.2.2.1, capacity_of_pre h]
  have savedInputX : (Operand.reg (savedInputRegister kind) : Operand 64).read x =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64) :=
    (hx.agrees.read (n := 64) (r := savedInputRegister kind) (by rcases hkind with rfl | rfl | rfl <;> simp [FinalizeReset.CompressCall.changes, savedInputRegister])).trans
      ((hi.agrees.read (n := 64) (r := savedInputRegister kind)
        (by rcases hkind with rfl | rfl | rfl <;> simp [incrementPrepareEffect, Effect.components, savedInputRegister])).trans savedInputV)
  have hv14 : (Operand.reg 14 : Operand 64).read v =
      BitVec.ofNat 64 (input.size - (64 - message.size % 64)) := by
    rw [hc.agrees.read (n := 64) (r := 14) (by rcases hkind with rfl | rfl | rfl <;> simp [callSiteChanges]),
      he.writes.2.2.1, capacity_of_pre h]
    have hsz : (Operand.reg kind.sizeRegister : Operand 64).read s = BitVec.ofNat 64 input.size := h.inputSize
    change (Operand.reg kind.sizeRegister : Operand 64).read s - _ = _
    rw [hsz]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by have := h.totalSize; omega)
  have hx14 : (Operand.reg 14 : Operand 64).read x =
      BitVec.ofNat 64 (input.size - (64 - message.size % 64)) :=
    (hx.agrees.read (n := 64) (r := 14) (by rcases hkind with rfl | rfl | rfl <;> simp [FinalizeReset.CompressCall.changes])).trans
      ((hi.agrees.read (n := 64) (r := 14)
        (by rcases hkind with rfl | rfl | rfl <;> simp [incrementPrepareEffect, Effect.components])).trans hv14)
  have hsize : input.size - (64 - message.size % 64) < 2^64 := by
    have := h.totalSize
    omega
  have hcount : (Operand.reg 14 : Operand 64).read x >>> 6 =
      BitVec.ofNat 64 ((input.size - (64 - message.size % 64)) / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [hx14]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt (show
      (input.size - (64 - message.size % 64)) / 64 < 2^64 by omega)]
  have hzero : (Operand.reg 14 : Operand 64).read x >>> 6 = 0 ↔
      (input.size - (64 - message.size % 64)) / 64 = 0 := by
    rw [hcount]
    constructor
    · intro hz
      have hn := congrArg BitVec.toNat hz
      change ((input.size - (64 - message.size % 64)) / 64) % 2^64 = 0 at hn
      rw [Nat.mod_eq_of_lt (by omega)] at hn
      exact hn
    · intro hz
      rw [hz]
      rfl
  obtain ⟨fc, hac⟩ := hc.advances
  obtain ⟨fx, hax⟩ := hx.advances
  refine ⟨t, ⟨⟨fu + fc + fw + fx + ft, (((hau.trans hac).trans haw).trans hax).trans hat⟩,
    hrt, hct, ?_, (hagx.trans (fillCountEffect_agrees hkind hxsp hf)).mono (by simp),
    by omega, hf.writes.2.1.trans savedInputX, ?_, hf.writes.2.2.trans hcount,
    htbuffer, htcount.trans ((hx.update_counter h hwsp hwdi).trans hwcount)⟩⟩
  · rw [hf.rip]
    change (if (Operand.reg 14 : Operand 64).read x >>> 6 = 0 then pc kind 0x100a4a else pc kind 0x100a35) = _
    simp only [hzero]
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.tailEntry, UpdateKind.batchEntry, pc]
  · have hr := (hf.agrees.read (n := 64) (r := 14)
      (by rcases hkind with rfl | rfl | rfl <;> simp [fillCountEffect, Effect.components, UpdateKind.inputRegister])).trans hx14
    rcases hkind with rfl | rfl | rfl <;> exact hr

end Md5.Proofs.Buffered.ResetSecond
