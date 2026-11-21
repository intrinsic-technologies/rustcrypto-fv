import Md5.Proofs.Buffered.Finalize.Streams.Slices.FinalBlockBytes
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Transition

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_lastBlock {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hOutside : ¬ InProgram boundary.rip) (h : LengthReady (update := update) message s) :
    ∃ t, Transition (update := update) boundary s t ∧ CallReady (update := update) message t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨n, u, hn, hu, hcu, hl⟩ := Blocks.Length.run (update := update)
      h.ready h.code h.toStorage hOutside h.rip
    have hus := h.toStorage.of_agrees hl.agrees (Blocks.Length.effect_rsp hl)
    obtain ⟨m, t, hm, ht, hct, hc⟩ := Blocks.Copy.run (update := update) (kind := .finalBlock)
      hu hcu hus hOutside hl.rip
    have hsu : Transition (update := update) boundary s u := ⟨⟨n, hn⟩, Blocks.Length.transition_agrees hl⟩
    have hut : Transition (update := update) boundary u t := ⟨⟨m, hm⟩, Blocks.Copy.transition_agrees hc⟩
    exact ⟨t, hsu.trans hut, lastBlock_ready h hl hc ht hct⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices
