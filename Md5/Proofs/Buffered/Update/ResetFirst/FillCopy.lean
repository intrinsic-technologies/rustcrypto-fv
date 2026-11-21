import Md5.Proofs.Buffered.Update.ResetFirst.FillReady
import Md5.Proofs.Buffered.Update.ResetFirst.Calls

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem fill_copy_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre kind boundary message input s)
    (he : (fillReadyEffect_of_kind kind s).Holds s u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ v, MemcpySiteResult boundary (pc kind 0x704) u v := by
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by rcases hk with rfl | rfl | rfl <;> simp [fillReadyEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister])
  have hsi : rsi.read u = (Operand.reg kind.inputRegister : Operand 64).read s +
      BitVec.ofNat 64 0 := by
    change (Operand.reg 6 : Operand 64).read u = (Operand.reg kind.inputRegister : Operand 64).read s + 0
    exact he.writes.2.2.2.2.2.trans (BitVec.add_zero _).symm
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64) :=
    he.writes.2.1.trans (capacity_of_pre_of_kind h)
  have hdi : rdi.read u = kind.context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.2.2.1, position_of_pre_of_kind h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 kind.contextOffset =
      stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hpre : MemcpySitePre (pc kind 0x704) u := h.memcpySitePre he.agrees hsp hdi hsi hdx
    (by omega) (by omega) (by rcases hk with rfl | rfl | rfl <;> decide) (Or.inl (by rcases hk with rfl | rfl | rfl <;> decide))
    (by rcases hk with rfl | rfl | rfl <;> simp [fillReadyEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister])
  have hslot : Memory.MemWritable u (pushAddr u) 8 := by
    have hw := h.callSlotWritable_of_agrees he.agrees
    simpa only [pushAddr, hsp] using hw
  have hpc : pc kind 0x6fe + 6 = pc kind 0x704 := by
    rcases hk with rfl | rfl | rfl <;> decide
  rw [← hpc] at hpre ⊢
  exact memcpy_rip_of_kind hk h.stride (Or.inr (Or.inl rfl)) h.boundaryOutside hr hc he.rip hslot hpre


theorem fill_copy [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (he : (fillReadyEffect s).Holds s u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ v, MemcpySiteResult boundary 0x100704 u v := by
  exact fill_copy_of_kind (kind := .resetFirst) (Or.inl rfl) h he hr hc hfull

end Md5.Proofs.Buffered.ResetFirst
