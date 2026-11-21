import Md5.Proofs.Buffered.FinalizeReset.Copy.Model
import Md5.Proofs.Buffered.FinalizeReset.Frame

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxHeartbeats 600000 in
@[local x86_local] theorem partEffect_local {variant : Variant} (kind : Kind) (part : Part) :
    Effect.Local (fun s ↦ partEffect kind part s variant) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · have hsp : stackPtr t = stackPtr t' := h.read (.reg 4 : Operand 64) trivial
    cases part <;> cases kind <;> simp [partEffect, wordWrite, hsp, h.read_mem]
  · simpa only [partEffect, Effect.flag] using congrArg some hi
  · cases part <;> cases kind <;> simp [partEffect, wordWrite, Write.Full, Operand.Full]

theorem part_cover {variant : Variant} {kind : Kind} {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect kind part s variant).components) {address : BitVec 64}
    (ha : c.Covers address) : Component.Covers (.mem (stackPtr s + 8) 152) address := by
  cases kind <;> cases part
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact Export.covers_shift (offset := 120)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 128)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 136)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 144)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact Export.covers_shift (offset := 88)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 96)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 104)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 112)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact Export.covers_shift (offset := 120)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 128)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 136)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact Export.covers_shift (offset := 88)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 96)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 104)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
    · exact Export.covers_shift (offset := 112)
        (by simpa only [stackPtr, Operand.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd] using ha) (by decide)
  · x86_norm [partEffect, wordWrite, stackPtr] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim

theorem part_agrees {variant : Variant} {kind : Kind} {part : Part} {s t : RamState}
    (h : (partEffect kind part s variant).Holds s t) :
    AgreesExcept (FinalizeReset.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    cases c <;> cases kind <;> cases part <;>
      simp_all only [partEffect, Effect.components, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append,
        wordWrite, Write.component, Operand.component, Component.isMem,
        FinalizeReset.changes, List.mem_cons, List.not_mem_nil, or_false,
        Component.reg.injEq, reduceCtorEq]
    all_goals grind
  · intro address c hc ha
    exact ⟨.mem (stackPtr s + 8) 152, by simp [FinalizeReset.changes], part_cover hc ha⟩

theorem part_avoids {variant : Variant} {kind : Kind} {part : Part} {s : RamState} (hs : Storage s variant) :
    (partEffect kind part s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  exact hs.stackAvoids _ (Export.stack_cover hs (by cases variant <;> decide : 8 + 152 ≤ variant.stackBytes)
    (part_cover hc ha)) (.inl ⟨x.2, hx⟩)

end Md5.Proofs.Buffered.FinalizeReset.Copy
