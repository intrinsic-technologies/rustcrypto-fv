import Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

@[local x86_local] theorem partEffect_local (part : Part) :
    Effect.Local (partEffect part) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · have hsp : stackPtr t = stackPtr t' := h.read (.reg 4 : Operand 64) trivial
    cases part <;> simp [partEffect, wordWrite, hsp, h.read_mem]
  · simpa only [partEffect, Effect.flag] using congrArg some hi
  · cases part <;> simp [partEffect, wordWrite, Write.Full, Operand.Full]

theorem part_components {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect part s).components) : c ∈ (effect s).components := by
  cases part <;>
    simp_all [partEffect, effect, wordWrite, List.range_succ, List.range_zero,
      Effect.components]
  all_goals grind

theorem part_rsp {part : Part} {s t : RamState}
    (h : (partEffect part s).Holds s t) : stackPtr t = stackPtr s := by
  apply (h.agrees.mono (fun _ hc ↦ part_components hc)).read (n := 64) (r := 4)
  simp [effect, wordWrite, Effect.components, List.range_succ, List.range_zero]

theorem part_avoids {part : Part} {s : RamState} (hs : Storage .digest s) :
    (partEffect part s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  exact effect_avoids hs x hx c (part_components hc) ha

end Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy
