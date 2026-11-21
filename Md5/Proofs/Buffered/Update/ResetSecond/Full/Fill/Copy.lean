import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Ready
import Md5.Proofs.Buffered.Update.ResetSecond.Calls
import Md5.Proofs.Buffered.Update.Fill.Copy

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem fill_copy [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (he : (fillReadyEffect kind s).Holds s u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ v, MemcpySiteResult boundary (pc kind 0x100a0d) u v := by
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by rcases hkind with rfl | rfl | rfl <;> simp [fillReadyEffect, Effect.components, positionRegister, savedInputRegister])
  have hsi : rsi.read u = (Operand.reg kind.inputRegister : Operand 64).read s +
      BitVec.ofNat 64 0 := by
    exact he.writes.2.2.2.2.2.trans (BitVec.add_zero _).symm
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64) :=
    he.writes.2.1.trans (capacity_of_pre h)
  have hdi : rdi.read u = kind.context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.2.2.1, position_of_pre h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 kind.contextOffset =
      stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hpre : MemcpySitePre (pc kind 0x100a0d) u := h.memcpySitePre he.agrees hsp hdi hsi hdx
    (by omega) (by omega) (by rcases hkind with rfl | rfl | rfl <;> decide +kernel) (by rcases hkind with rfl | rfl | rfl <;> exact Or.inl (by decide +kernel))
    (by rcases hkind with rfl | rfl | rfl <;> simp [fillReadyEffect, Effect.components, positionRegister, savedInputRegister])
  have hslot : Memory.MemWritable u (pushAddr u) 8 := by
    have hw := h.callSlotWritable_of_agrees he.agrees
    simpa only [pushAddr, hsp] using hw
  have hr15 : (Operand.reg 15 : Operand 64).read u = 0x1024b0 := by
    rw [he.agrees.read (n := 64) (r := 15) (by
      rcases hkind with rfl | rfl | rfl <;> simp [fillReadyEffect, Effect.components, positionRegister, savedInputRegister])]
    rcases hkind with hk | hk | hk
    · exact (h.secondRegisters (Or.inl hk)).2
    · exact (h.secondRegisters (Or.inr hk)).2
    · exact h.discardSecondMemcpy hk
  have hrip : u.RIP = pc kind 0x100a0a := he.rip
  have hnext : pc kind 0x100a0a + 3 = pc kind 0x100a0d := by
    rcases hkind with rfl | rfl | rfl <;> decide +kernel
  obtain ⟨v, hv⟩ := memcpy_r15 h.stride (p := pc kind 0x100a0a)
    (by rcases hkind with rfl | rfl | rfl <;> decide +kernel)
    h.boundaryOutside hr hc hrip hr15 hslot
    (by simpa only [hnext] using hpre)
  refine ⟨v, ?_⟩
  simpa only [hnext] using hv

end Md5.Proofs.Buffered.ResetSecond
