import Sha1.Proofs.Buffered.Update.Slices.BranchState

import Sha1.Proofs.Buffered.Update.Slices.Short.Steps
import Sha1.Proofs.Buffered.Update.Slices.Short.Absorbed
import Sha1.Proofs.Buffered.Update.Slices.Frame

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short [bindings : Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (b : BranchState boundary message input s u)
    (hsize : input.size < 64 - message.size % 64) :
    ∃ t, UpdatePost .updateFinalize boundary message input s t := by
  obtain ⟨np, p, hap, hrp, hcp, hipp, hdi, hsi, hdx, hagp⟩ :=
    short_prepare b.ready b.code h.boundaryOutside (by simpa only [ite_eq_left hsize] using b.rip)
  have ha := b.agrees.trans hagp
  have hsp : stackPtr p = stackPtr s := ha.read (n := 64) (r := 4) (by simp)
  have husp : stackPtr u = stackPtr s := b.agrees.read (n := 64) (r := 4) (by simp)
  have hdst : rdi.read p = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [hdi, husp, b.position]
    change _ = stackPtr s + 216 + _
    ac_rfl
  have hsrc : rsi.read p = (Operand.reg 14 : Operand 64).read s :=
    hsi.trans (b.agrees.read (by simp))
  have hlen : MemoryRoutines.rdx.read p = BitVec.ofNat 64 input.size :=
    hdx.trans ((b.agrees.read (by simp)).trans h.inputSize)
  obtain ⟨v, hv⟩ := copy_input h ha hsp hrp hcp (ha.directionFlagClear (by simp) ⟨h.df⟩).df
    hipp (.inl rfl) (src := 0) (by simpa only [BitVec.add_zero] using hsrc) hdst hlen
    (by omega) (by omega)
  have hvsp := hv.rsp.trans hsp
  have hhigh : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 216 :=
    toNat_add_ofNat _ 216 (by omega)
  have hpos : stackPtr v + 279 = UpdateKind.updateFinalize.context s + 63 := by
    rw [hvsp]
    change stackPtr s + 279 = stackPtr s + 216 + 63
    rw [BitVec.add_assoc]
    rfl
  have hpn : (stackPtr v + 279).toNat = (stackPtr s).toNat + 279 := by
    rw [hvsp]; exact toNat_add_ofNat _ 279 (by omega)
  have hw : MemoryRoutines.WritableRange v (stackPtr v + 279) 1 := by
    refine DigestPrepare.writableRange_of_region ?_ (allocated_of_agrees (ha.trans hv.agrees) h.contextAllocated) h.contextAvoids ?_ ?_
    · change (UpdateKind.updateFinalize.context s).toNat + 92 < 2^32
      omega
    · change (UpdateKind.updateFinalize.context s).toNat ≤ _
      omega
    · change _ ≤ (UpdateKind.updateFinalize.context s).toNat + 92
      omega
  obtain ⟨nt, t, hat, hrt, hct, hit, hp, hagt⟩ := short_finish hv.ready hv.code
    h.boundaryOutside hv.rip hw
  rw [hpos] at hp hagt
  have hv3 : (Operand.reg 3 : Operand 64).read v = BitVec.ofNat 64 input.size :=
    ((ha.trans hv.agrees).read (by simp [callSiteChanges])).trans h.inputSize
  have hv13 : (Operand.reg 13 : Operand 64).read v = BitVec.ofNat 64 (message.size % 64) :=
    ((hagp.trans hv.agrees).read (by simp [callSiteChanges])).trans b.position
  have hp' : (Operand.mem (UpdateKind.updateFinalize.context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size) := by
    rw [hp]
    change ((Operand.reg 3 : Operand 64).read v).setWidth 8 +
      ((Operand.reg 13 : Operand 64).read v).setWidth 8 = _
    rw [hv3, hv13]
    simp only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), ← BitVec.ofNat_add, Nat.add_comm]
  obtain ⟨nb, hab⟩ := b.advances
  obtain ⟨nv, hav⟩ := hv.advances
  refine ⟨t, ⟨⟨_, ((hab.trans hap).trans hav).trans hat⟩, hrt, hct, by simp [hit, UpdateKind.exits],
    short_absorbed h hsize (ha.external (by simp [Component.Covers])) hsp hdst hsrc hlen hv hagt hp', ?_⟩⟩
  have hf : AgreesExcept (UpdateKind.updateFinalize.changes s) v t := by
    apply hagt.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals simp [UpdateKind.changes, UpdateKind.workRegisters, Component.isMem] at hm ⊢
    · intro x c hc hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact hx.elim
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨.mem (UpdateKind.updateFinalize.context s) 92, by simp [UpdateKind.changes],
        63 + i, by omega, ?_⟩
      simp only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
  have hg := (ha.trans (copy_agrees h hv hsp hdst hlen (by omega))).trans hf
  apply hg.mono
  simp [UpdateKind.changes, UpdateKind.workRegisters]

end Sha1.Proofs.Buffered.Update.Slices
