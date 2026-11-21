import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Streams.Slices.PaddingRun
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem padding_agrees {update : Bool} {s t : RamState} {n : Nat}
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (paddingEffect (update := update) s).Holds s t) : AgreesExcept ((streamKind update).changes s) s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    apply he.agrees.widen
    · intro c hc hm
      simp only [paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [streamKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · intro address c hc hcover
      refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges], ?_⟩
      simp only [paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      apply FinalizeReset.Export.covers_shift (offset := n + 16) (len := 1) _ (by omega)
      rw [hp] at hcover
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using hcover

theorem call_agrees {update : Bool} [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {offset : Nat} (h : CallSiteResult boundary ret s t)
    (hdst : rdi.read s = stackPtr s + BitVec.ofNat 64 offset)
    (hlen : offset + (MemoryRoutines.rdx.read s).toNat ≤ 168) :
    AgreesExcept ((streamKind update).changes s) s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    apply h.agrees.widen
    · intro c hc hm
      simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [streamKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · intro address c hc hcover
      simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges], ?_⟩
        rw [hdst] at hcover
        exact FinalizeReset.Export.covers_shift hcover hlen
      · refine ⟨.mem (stackPtr s - 320) 320, by simp [streamKind, Kind.changes], ?_⟩
        have hpush : pushAddr s = stackPtr s - 320 + BitVec.ofNat 64 312 := by
          simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          rfl
        rw [hpush] at hcover
        exact FinalizeReset.Export.covers_shift hcover (by decide)

end Md5.Proofs.Buffered.Finalize.Streams.Slices
