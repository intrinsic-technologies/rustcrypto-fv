import Md5.Proofs.Buffered.Update.ResetSecond.ShortReady
import Md5.Proofs.Buffered.Update.ResetSecond.Calls
import Md5.Proofs.Buffered.Update.ResetSecond.Position
import Md5.Proofs.Buffered.Update.ResetSecond.ShortMemory

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short_update [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ t, UpdatePost kind boundary message input s t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := short_ready hkind h hshort
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, positionRegister, UpdateKind.sizeRegister, Effect.components])
  have hdi : rdi.read u = kind.context s +
      BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.1, position_of_pre h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 kind.contextOffset =
      stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hsi : rsi.read u = (Operand.reg kind.inputRegister : Operand 64).read s := by
    rcases hkind with rfl | rfl | rfl
    · exact he.agrees.read (by simp [shortReadyEffect, positionRegister, Effect.components])
    · exact he.agrees.read (by simp [shortReadyEffect, positionRegister, Effect.components])
    · exact he.writes.2.2.2.2
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 input.size := by
    rcases hkind with rfl | rfl | rfl
    · exact he.writes.2.2.2.trans h.inputSize
    · exact he.writes.2.2.2.trans h.inputSize
    · exact he.writes.2.2.2.1.trans h.inputSize
  have hdxn : (MemoryRoutines.rdx.read u).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr15 : (Operand.reg 15 : Operand 64).read u = 0x1024b0 := by
    have hp : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read s :=
      he.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, positionRegister, Effect.components])
    rw [hp]
    rcases hkind with rfl | rfl | rfl
    · exact (h.secondRegisters (Or.inl rfl)).2
    · exact (h.secondRegisters (Or.inr rfl)).2
    · exact h.discardSecondMemcpy rfl
  have hslot : Memory.MemWritable u (pushAddr u) 8 := by
    simpa only [pushAddr, hsp] using h.callSlotWritable_of_agrees he.agrees
  have hcopyPre : MemcpySitePre (pc kind 0x1009ae) u := h.memcpySitePre (offset := 0) he.agrees hsp hdi
    (hsi.trans (BitVec.add_zero _).symm) hdx (by omega)
    (by omega) (by rcases hkind with rfl | rfl | rfl <;> decide +kernel)
    (by left; rcases hkind with rfl | rfl | rfl <;> decide +kernel)
    (by rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, positionRegister, UpdateKind.sizeRegister, Effect.components])
  obtain ⟨v, hc⟩ := memcpy_r15 h.stride (by rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, pc]) h.boundaryOutside hru hcu he.rip hr15
    hslot (by rcases hkind with rfl | rfl | rfl <;> exact hcopyPre)
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans hsp
  obtain ⟨t, htadv, ht, hct, htrip, hp, ha⟩ := short_finish hkind h (he.agrees.trans hc.agrees)
    hvsp hc.ready hc.code (by rcases hkind with rfl | rfl | rfl <;> exact hc.rip)
  have hext : u.external = s.external := he.agrees.external (by
    rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, Effect.components, Component.Covers])
  have haddr : kind.context v + 63 = kind.context s + 63 := by
    simp only [UpdateKind.context, hvsp]
  have hm : ∀ c : Component, c ∈ [.reg kind.sizeRegister, .flags, .rip, .mem (kind.context v + 63) 1] →
      ∀ address, c.Covers address → address = kind.context s + 63 := by
    intro c hc' address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    simpa only [BitVec.add_zero] using haddr
  have hv12 : (Operand.reg kind.sizeRegister : Operand 64).read v = BitVec.ofNat 64 input.size :=
    ((hc.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [callSiteChanges, UpdateKind.sizeRegister])).trans
      (he.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [shortReadyEffect, positionRegister, UpdateKind.sizeRegister, Effect.components]))).trans h.inputSize
  have hv13 : (Operand.reg (positionRegister kind) : Operand 64).read v = BitVec.ofNat 64 (message.size % 64) :=
    ((hc.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [callSiteChanges, positionRegister])).trans he.writes.1).trans (position_of_pre h)
  have hpos : (Operand.mem (kind.context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size) := by
    rw [haddr] at hp
    rw [hp]
    change ((Operand.reg kind.sizeRegister : Operand 64).read v).setWidth 8 +
      ((Operand.reg (positionRegister kind) : Operand 64).read v).setWidth 8 = _
    rw [hv12, hv13]
    simp only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), ← BitVec.ofNat_add, Nat.add_comm]
  have hag0 : AgreesExcept (kind.changes s) s u := by
    apply he.agrees.mono
    intro c hc'
    rcases hkind with rfl | rfl | rfl
    all_goals simp only [shortReadyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, reduceCtorEq, ite_false, ite_true, List.append_nil,
      positionRegister, UpdateKind.sizeRegister] at hc'
    all_goals first
      | (rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp [UpdateKind.changes, UpdateKind.workRegisters]
  have hag1 := hc.toCallSiteResult.update_agrees h hsp hdi (by rw [hdxn]; omega)
  have hag2 := short_finish_update_agrees hvsp ha
  obtain ⟨fc, hac⟩ := hc.advances
  refine ⟨t, ⟨⟨fu + fc + 2, (hau.trans hac).trans htadv⟩, ht, hct,
    by
      rw [htrip]
      rcases hkind with rfl | rfl | rfl <;> decide +kernel, ?_, ?_⟩⟩
  · exact short_absorbed_after_finish h hshort hc hext hsp hdi hsi hdx ha hm hpos
  · exact (hag0.trans (hag1.trans hag2)).mono (by simp)

end Md5.Proofs.Buffered.ResetSecond
