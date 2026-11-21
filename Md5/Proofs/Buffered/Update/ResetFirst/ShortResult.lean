import Md5.Proofs.Buffered.Update.ResetFirst.ShortCopy
import Md5.Proofs.Buffered.Update.ResetFirst.ShortFinish
import Md5.Proofs.Buffered.Update.Short.Memory

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short_result_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v t : RamState} (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64)
    (he : (shortReadyEffect_of_kind kind s).Holds s u)
    (hu : ∃ fuel, Advances boundary fuel s u)
    (hc : MemcpySiteResult boundary (pc kind 0x6a4) u v)
    (ht : ∃ fuel, Advances boundary fuel v t)
    (hr : ReadyToStep t) (hcode : CodeIn Extracted.programImage t)
    (hf : (shortFinishEffect_of_kind kind v).Holds v t) :
    UpdatePost kind boundary message input s t := by
  have hrip : t.RIP = (pc kind 0x6ac) := hf.rip
  have ha : AgreesExcept [.reg kind.sizeRegister, .flags, .rip, .mem (stackPtr v + stackOffset kind 71) 1] v t := by
    apply hf.agrees.mono
    intro c hm
    rcases hk with rfl | rfl | rfl <;>
      simpa [shortFinishEffect_of_kind, stackOffset, UpdateKind.contextOffset, Effect.components, or_assoc, or_left_comm, or_comm] using hm
  have hp : (Operand.mem (stackPtr v + stackOffset kind 71) : Operand 8).read t =
      (Operand.reg kind.sizeRegister : Operand 8).read v + (Operand.reg (reg kind 13) : Operand 8).read v := hf.writes.2
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by rcases hk with rfl | rfl | rfl <;> simp [shortReadyEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister])
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans hsp
  have hdi : rdi.read u = kind.context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.1, position_of_pre_of_kind h]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 kind.contextOffset =
      stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hsi : rsi.read u = (Operand.reg kind.inputRegister : Operand 64).read s := he.writes.2.2.2.1
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 input.size :=
    he.writes.2.2.2.2.trans h.inputSize
  have hdxn : (MemoryRoutines.rdx.read u).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hext : u.external = s.external := he.agrees.external (by
    simp [shortReadyEffect_of_kind, Effect.components, Component.Covers])
  have haddr : stackPtr v + stackOffset kind 71 = kind.context s + 63 := by
    rw [hvsp]
    change stackPtr s + stackOffset kind 71 = stackPtr s + BitVec.ofNat 64 kind.contextOffset + 63
    rw [BitVec.add_assoc]
    rcases hk with rfl | rfl | rfl <;> rfl
  have hm : ∀ c : Component, c ∈ [.reg kind.sizeRegister, .flags, .rip, .mem (stackPtr v + stackOffset kind 71) 1] →
      ∀ address, c.Covers address → address = kind.context s + 63 := by
    intro c hc' address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    simpa only [BitVec.add_zero] using haddr
  have hv14 : (Operand.reg kind.sizeRegister : Operand 64).read v = BitVec.ofNat 64 input.size :=
    ((hc.agrees.read (by rcases hk with rfl | rfl | rfl <;> simp [callSiteChanges, UpdateKind.sizeRegister])).trans
      (he.agrees.read (by rcases hk with rfl | rfl | rfl <;> simp [shortReadyEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister]))).trans h.inputSize
  have hv13 : (Operand.reg (reg kind 13) : Operand 64).read v = BitVec.ofNat 64 (message.size % 64) :=
    ((hc.agrees.read (by rcases hk with rfl | rfl | rfl <;> simp [callSiteChanges, reg])).trans he.writes.1).trans (position_of_pre_of_kind h)
  have hpos : (Operand.mem (kind.context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size) := by
    rw [haddr] at hp
    rw [hp]
    change ((Operand.reg kind.sizeRegister : Operand 64).read v).setWidth 8 +
      ((Operand.reg (reg kind 13) : Operand 64).read v).setWidth 8 = _
    rw [hv14, hv13]
    simp only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), ← BitVec.ofNat_add,
      Nat.add_comm]
  have hag0 : AgreesExcept (kind.changes s) s u := by
    apply he.agrees.mono
    intro c hc'
    simp only [shortReadyEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, reg]
  have hag1 := hc.toCallSiteResult.update_agrees h hsp hdi (by rw [hdxn]; omega)
  have hag2 : AgreesExcept (kind.changes s) v t := by
    apply ha.widen
    · intro c hc' hm'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl
      · rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, UpdateKind.sizeRegister]
      · simp [UpdateKind.changes]
      · simp [UpdateKind.changes]
      · exact Bool.noConfusion hm'
    · intro address c hc' hcover
      refine ⟨.mem (kind.context s) 88, by simp [UpdateKind.changes],
        63, by decide, ?_⟩
      exact hm c hc' address hcover
  obtain ⟨fu, hau⟩ := hu
  obtain ⟨fc, hac⟩ := hc.advances
  obtain ⟨ft, hat⟩ := ht
  refine ⟨⟨fu + fc + ft, (hau.trans hac).trans hat⟩, hr, hcode,
    by rw [hrip]; rcases hk with rfl | rfl | rfl <;> decide, ?_, ?_⟩
  · exact short_absorbed_after_finish h hshort hc hext hsp hdi hsi hdx ha hm hpos
  · exact (hag0.trans (hag1.trans hag2)).mono (by simp)


theorem short_result [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v t : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hshort : message.size % 64 + input.size < 64)
    (he : (shortReadyEffect s).Holds s u)
    (hu : ∃ fuel, Advances boundary fuel s u)
    (hc : MemcpySiteResult boundary 0x1006a4 u v)
    (ht : ∃ fuel, Advances boundary fuel v t)
    (hr : ReadyToStep t) (hcode : CodeIn Extracted.programImage t)
    (hf : (shortFinishEffect v).Holds v t) :
    UpdatePost .resetFirst boundary message input s t := by
  exact short_result_of_kind (kind := .resetFirst) (Or.inl rfl) h hshort he hu hc ht hr hcode hf

end Md5.Proofs.Buffered.ResetFirst
