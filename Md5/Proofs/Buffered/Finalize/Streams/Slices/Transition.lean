import Md5.Proofs.Buffered.Finalize.Streams.Slices.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Transition [Bindings] (boundary : ReturnBoundary) (s t : RamState) (update : Bool := false) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  agrees : AgreesExcept ((streamKind update).changes s) s t

theorem Transition.rsp {update : Bool} [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    (h : Transition (update := update) boundary s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by
    cases update <;> simp [streamKind, Kind.changes, Kind.workRegisters, Kind.localChanges])

theorem Transition.trans {update : Bool} [Bindings] {boundary : ReturnBoundary} {s t u : RamState}
    (h : Transition (update := update) boundary s t) (h' : Transition (update := update) boundary t u) :
    Transition (update := update) boundary s u := by
  obtain ⟨n, hn⟩ := h.advances
  obtain ⟨m, hm⟩ := h'.advances
  refine ⟨⟨n + m, hn.trans hm⟩, ?_⟩
  have hc : (streamKind update).changes t = (streamKind update).changes s := by
    cases update <;> simp only [streamKind, Bool.false_eq_true, ↓reduceIte, Kind.changes, Kind.localChanges, h.rsp]
  have ha := h'.agrees
  rw [hc] at ha
  apply (h.agrees.trans ha).mono
  intro c hc
  simpa only [List.mem_append, or_self] using hc

end Md5.Proofs.Buffered.Finalize.Streams.Slices
