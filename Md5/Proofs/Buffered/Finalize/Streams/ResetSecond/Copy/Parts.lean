import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Model
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem part_rsp {variant : Variant} {kind : Kind} {part : Part} {s t : RamState}
    (h : (partEffect kind part s variant).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> cases part <;> simp [partEffect, wordWrite, Effect.components]

theorem part_avoids {variant : Variant} {kind : Kind} {part : Part} {s : RamState}
    (hs : Storage variant.toKind s) : (partEffect kind part s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  cases kind <;> cases part <;>
    simp only [partEffect, wordWrite, Effect.components, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals exact hs.stackAvoids _ (hs.stackCover (by cases variant <;> decide) ha) (.inl ⟨x.2, hx⟩)

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy
