import Md5.Proofs.Buffered.Update.Fill.Memory
import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

set_option maxRecDepth 4096 in
theorem filledBlock_of_copy [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState} {ret : BitVec 64}
    (h : UpdatePre kind boundary message input initial)
    (hc : MemcpySiteResult boundary ret s t) (hext : s.external = initial.external)
    (hsp : stackPtr s = stackPtr initial)
    (hdi : rdi.read s = kind.context initial + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read s = (Operand.reg kind.inputRegister : Operand 64).read initial)
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 (64 - message.size % 64))
    (hfull : 64 - message.size % 64 ≤ input.size) :
    (⟨(kind.context initial).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      (updateBlock message input) ∧
    (⟨(kind.context initial).toNat + 64, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ ∧
    (Operand.mem (kind.context initial + 80) : Operand 64).read t =
      BitVec.ofNat 64 (message.size / 64) := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have hcount : (MemoryRoutines.rdx.read s).toNat = 64 - message.size % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsize : (input.extract 0 (64 - message.size % 64)).size =
      64 - message.size % 64 := by simp only [ByteArray.size_extract]; omega
  have hdst : (rdi.read s).toNat = (kind.context initial).toNat + message.size % 64 := by
    rw [hdi]
    exact toNat_add_ofNat _ _ (by omega)
  have hsrc : (⟨(rsi.read s).toNat, (input.extract 0 (64 - message.size % 64)).size⟩ :
      MemoryRegion).HasBytes s.external (input.extract 0 (64 - message.size % 64)) := by
    rw [hext, hsi]
    simpa only [Nat.add_zero, UpdateKind.inputRegion] using
      hasBytes_extract h.inputBytes 0 (64 - message.size % 64)
  have hcopy := hc.hasBytes (hcount.trans hsize.symm) hsrc
  apply filledBlock_of_frame h hfull ?_
  · simpa only [hdst, hsize] using hcopy
  · intro address hout
    calc
      t.external[address]? = s.external[address]? := by
        apply hc.agrees.byte
        intro c hm hcover
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        · apply hout ⟨(kind.context initial).toNat + message.size % 64,
            64 - message.size % 64⟩ (by simp [fillWriteRegions])
          apply contains_of_mem_covers (by
            change (kind.context initial).toNat + message.size % 64 +
              (64 - message.size % 64) < 2^32
            omega)
          simpa only [hdi, hcount, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            using hcover
        · apply hout (UpdateKind.scratchRegion initial) (by simp [fillWriteRegions])
          obtain ⟨i, hi, rfl⟩ := hcover
          have hpush : (pushAddr s).toNat = (stackPtr initial).toNat - 8 := by
            change (stackPtr s - 8).toNat = _
            rw [hsp]
            exact BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr initial).toNat; omega)
          rw [toNat_add_ofNat _ _ (by rw [hpush]; have := (stackPtr initial).isLt; omega), hpush]
          change (stackPtr initial).toNat - 320 ≤ _ ∧
            _ < (stackPtr initial).toNat - 320 + 320
          omega
      _ = initial.external[address]? := by rw [hext]

end Md5.Proofs.Buffered
