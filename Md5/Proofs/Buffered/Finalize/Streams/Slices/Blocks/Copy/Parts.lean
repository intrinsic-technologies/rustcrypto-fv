import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem part_components {update : Bool} {kind : Kind} {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect (update := update) kind part s).components) : c ∈ (effect (update := update) kind s).components := by
  cases kind <;> cases part <;>
    simp_all [partEffect, effect, wordWrite, Kind.words, List.range_succ, List.range_zero,
      Effect.components]
  all_goals grind

theorem part_rsp {update : Bool} {kind : Kind} {part : Part} {s t : RamState}
    (h : (partEffect (update := update) kind part s).Holds s t) : stackPtr t = stackPtr s := by
  apply (h.agrees.mono (fun _ hc ↦ part_components (update := update) hc)).read (n := 64) (r := 4)
  cases kind <;> simp [effect, wordWrite, Effect.components, Kind.words,
    List.range_succ, List.range_zero]

theorem part_avoids {update : Bool} {kind : Kind} {part : Part} {s : RamState} (hs : Storage (streamKind update) s) :
    (partEffect (update := update) kind part s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  exact effect_avoids (update := update) hs x hx c (part_components (update := update) hc) ha

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
