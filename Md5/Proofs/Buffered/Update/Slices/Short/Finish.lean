import Md5.Proofs.Buffered.Update.Slices.Short.Copy
import Md5.Proofs.Buffered.Update.Short.Memory

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short_result [Bindings] {variant : Bool} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v t : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hshort : message.size % 64 + input.size < 64)
    (he : ((shortReadyEffect variant) s).Holds s u)
    (hu : ∃ fuel, Advances boundary fuel s u)
    (hc : MemcpySiteResult boundary (pc variant 0x100327) u v)
    (ht : ∃ fuel, Advances boundary fuel v t)
    (hr : ReadyToStep t) (hcode : CodeIn Extracted.programImage t)
    (hrip : t.RIP = (pc variant 0x100331))
    (ha : AgreesExcept [.reg 3, .flags, .rip, .mem (stackPtr v + 255) 1] v t)
    (hp : (Operand.mem (stackPtr v + 255) : Operand 8).read t =
      (Operand.reg 3 : Operand 8).read v + (Operand.reg 13 : Operand 8).read v) :
    UpdatePost (kind variant) boundary message input s t := by
  have hsp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by simp [shortReadyEffect, Effect.components])
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans hsp
  have hdi : rdi.read u = (kind variant).context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [he.writes.2.2.1, position_eq h, kind_context]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + 192 =
      stackPtr s + 192 + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hsi : rsi.read u = (Operand.reg 14 : Operand 64).read s := he.writes.2.2.2.1
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 input.size :=
    he.writes.2.2.2.2.trans (by simpa only [kind_sizeRegister] using h.inputSize)
  have hdxn : (MemoryRoutines.rdx.read u).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hext : u.external = s.external := he.agrees.external (by
    simp [shortReadyEffect, Effect.components, Component.Covers])
  have haddr : stackPtr v + 255 = (kind variant).context s + 63 := by
    rw [hvsp, kind_context]
    change stackPtr s + 255 = stackPtr s + 192 + 63
    rw [BitVec.add_assoc]
    rfl
  have hm : ∀ c : Component, c ∈ [.reg 3, .flags, .rip, .mem (stackPtr v + 255) 1] →
      ∀ address, c.Covers address → address = (kind variant).context s + 63 := by
    intro c hc' address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    simpa only [BitVec.add_zero] using haddr
  have hv3 : (Operand.reg 3 : Operand 64).read v = BitVec.ofNat 64 input.size :=
    ((hc.agrees.read (by simp [callSiteChanges])).trans
      (he.agrees.read (by simp [shortReadyEffect, Effect.components]))).trans (by simpa only [kind_sizeRegister] using h.inputSize)
  have hv13 : (Operand.reg 13 : Operand 64).read v = BitVec.ofNat 64 (message.size % 64) :=
    ((hc.agrees.read (by simp [callSiteChanges])).trans he.writes.1).trans (position_eq h)
  have hpos : (Operand.mem ((kind variant).context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size) := by
    rw [haddr] at hp
    rw [hp]
    change ((Operand.reg 3 : Operand 64).read v).setWidth 8 +
      ((Operand.reg 13 : Operand 64).read v).setWidth 8 = _
    rw [hv3, hv13]
    simp only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), ← BitVec.ofNat_add, Nat.add_comm]
  have hag0 : AgreesExcept ((kind variant).changes s) s u := by
    apply he.agrees.mono
    intro c hc'
    simp only [shortReadyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters]
  have hag1 := hc.toCallSiteResult.update_agrees h hsp hdi (by rw [hdxn]; omega)
  have hag2 : AgreesExcept ((kind variant).changes s) v t := by
    apply ha.widen
    · intro c hc' hm'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl
      all_goals cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters, Component.isMem] at hm' ⊢
    · intro address c hc' hcover
      refine ⟨.mem ((kind variant).context s) 88, by simp [UpdateKind.changes],
        63, by decide, ?_⟩
      exact hm c hc' address hcover
  obtain ⟨fu, hau⟩ := hu
  obtain ⟨fc, hac⟩ := hc.advances
  obtain ⟨ft, hat⟩ := ht
  refine ⟨⟨fu + fc + ft, (hau.trans hac).trans hat⟩, hr, hcode,
    by cases variant <;> simpa [kind, pc, UpdateKind.exits] using Or.inl hrip, ?_, ?_⟩
  · exact short_absorbed_after_finish h hshort hc hext hsp hdi (by simpa only [kind_inputRegister] using hsi) hdx ha hm hpos
  · exact (hag0.trans (hag1.trans hag2)).mono (by simp)

end Md5.Proofs.Buffered.Update.Slices
