import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Slices.Full.Machine.Control

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def fullEntryEffect (variant : Bool) (s : RamState) : Effect :=
  { entryEffect variant s with
    rip := if position s = 0 then (pc variant 0x10041d) else (pc variant 0x100377)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem full_entry {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) (hfull : 64 - message.size % 64 ≤ input.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fullEntryEffect variant s).Holds s t := by
  obtain ⟨v, hav, hrv, hcv, hpcv, hagv⟩ := branch h hp
  rw [ite_eq_right (by omega)] at hpcv
  obtain ⟨fuel, t, hat, hrt, hct, he⟩ :=
    partial_branch boundary h.boundaryOutside v hrv hcv hpcv
  have hv13 : (Operand.reg 13 : Operand 64).read v = position s :=
    (hagv.read (by simp)).trans hp.effect.writes.1
  have hv2 : (Operand.reg 2 : Operand 64).read v = 64 - position s :=
    (hagv.read (by simp)).trans hp.effect.writes.2.1
  have hv5 : (Operand.reg 5 : Operand 64).read v =
      (Operand.reg 3 : Operand 64).read s - (64 - position s) :=
    (hagv.read (by simp)).trans hp.effect.writes.2.2
  obtain ⟨oldFuel, ha⟩ := hp.advances
  refine ⟨oldFuel + 1 + fuel, t, (ha.trans hav).trans hat, hrt, hct, ?_⟩
  refine ⟨?_, ?_, by trivial, ?_⟩
  · simpa only [partialEffect, fullEntryEffect, hv13] using he.rip
  · exact ⟨(he.agrees.read (by simp [partialEffect, Effect.components])).trans hv13,
      (he.agrees.read (by simp [partialEffect, Effect.components])).trans hv2,
      (he.agrees.read (by simp [partialEffect, Effect.components])).trans hv5⟩
  · apply ((hp.effect.agrees.trans hagv).trans he.agrees).mono
    simp [entryEffect, fullEntryEffect, partialEffect, Effect.components]

theorem capacity_eq {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre (kind variant) boundary message input s) :
    64 - position s = BitVec.ofNat 64 (64 - message.size % 64) := by
  rw [position_eq h]
  exact BitVec.ofNat_sub_ofNat_of_le 64 (message.size % 64) (by omega) (by omega)

end Md5.Proofs.Buffered.Update.Slices
