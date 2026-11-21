import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Entry
import Md5.Proofs.Buffered.Update.Slices.Full.Machine.Preparation

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def fillReadyEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x100389)
    writes := [⟨(.reg 13 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position s⟩,
      ⟨(.reg 5 : Operand 64), (.reg 3 : Operand 64).read s - (64 - position s)⟩,
      ⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s + (64 - position s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position s + 192⟩,
      ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_ready {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) (hfull : 64 - message.size % 64 ≤ input.size)
    (hpos : message.size % 64 ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fillReadyEffect variant s).Holds s t := by
  obtain ⟨fu, v, hav, hrv, hcv, he⟩ := full_entry h hp hfull
  have hpne : position s ≠ 0 := by
    intro hz
    have hn := congrArg BitVec.toNat hz
    rw [position_eq h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.size % 64 < 2^64 by omega)] at hn
    exact hpos hn
  have hip : v.RIP = (pc variant 0x100377) := by
    simpa only [fullEntryEffect, hpne, ite_false] using he.rip
  have hbytes : CodeIn (codeRange (pc variant 0x100377) fillCopyBytes) v :=
    by
      cases variant with
      | false => exact program_text_slice hcv 0x377 18 (by decide +kernel)
      | true => exact program_text_slice hcv 0x1927 18 (by decide +kernel)
  obtain ⟨ft, t, hat, hrt, _, hf⟩ :=
    fill_copy_prepare boundary h.boundaryOutside v hrv hbytes hip
  have hct := hf.agrees.codeIn (by
    simp [fillCopyEffect, Effect.components, Component.Covers]) hcv
  have hvsp : stackPtr v = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by simp [fullEntryEffect, entryEffect, Effect.components])
  have hv14 : (.reg 14 : Operand 64).read v = (.reg 14 : Operand 64).read s :=
    he.agrees.read (by simp [fullEntryEffect, entryEffect, Effect.components])
  have hv13 : (.reg 13 : Operand 64).read v = position s := he.writes.1
  have hv2 : (.reg 2 : Operand 64).read v = 64 - position s := he.writes.2.1
  refine ⟨fu + ft, t, hav.trans hat, hrt, hct, hf.rip, ?_, by trivial, ?_⟩
  · refine ⟨(hf.agrees.read (by simp [fillCopyEffect, Effect.components])).trans he.writes.1,
      (hf.agrees.read (by simp [fillCopyEffect, Effect.components])).trans he.writes.2.1,
      (hf.agrees.read (by simp [fillCopyEffect, Effect.components])).trans he.writes.2.2,
      ?_, ?_, ?_⟩
    · exact hf.writes.1.trans (by rw [hv14, hv2])
    · exact hf.writes.2.1.trans (by rw [hvsp, hv13])
    · exact hf.writes.2.2.trans hv14
  · apply (he.agrees.trans hf.agrees).mono
    simp only [fullEntryEffect, entryEffect, fillCopyEffect, fillReadyEffect,
      Effect.components, List.map_cons, List.map_nil, Write.component_reg,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp

end Md5.Proofs.Buffered.Update.Slices
