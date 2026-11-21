import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.PaddingRun
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 600000 in
theorem padding_agrees {variant : Variant} {s t : RamState} {n : Nat}
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (paddingEffect s variant).Holds s t) : AgreesExcept (variant.toKind.changes s) s t := by
  cases variant with
  | original =>
      apply he.agrees.widen
      · intro c hc hm
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        refine ⟨.mem (stackPtr s + BitVec.ofNat 64 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        apply FinalizeReset.Export.covers_shift (offset := n) (len := 1) _ (by omega)
        rw [hp] at hcover
        simpa only [ BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n) (BitVec.ofNat 64 96)] using hcover
  | finalize =>
      apply he.agrees.widen
      · intro c hc hm
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        refine ⟨.mem (stackPtr s + BitVec.ofNat 64 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        apply FinalizeReset.Export.covers_shift (offset := n) (len := 1) _ (by omega)
        rw [hp] at hcover
        simpa only [ BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n) (BitVec.ofNat 64 96)] using hcover
  | discard =>
      apply he.agrees.widen
      · intro c hc hm
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        refine ⟨.mem (stackPtr s + BitVec.ofNat 64 120) 168, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
        apply FinalizeReset.Export.covers_shift (offset := 16) (len := 88) _ (by decide)
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        change Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 136) 88) address
        simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, Write.component, Operand.component, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        apply FinalizeReset.Export.covers_shift (offset := n) (len := 1) _ (by omega)
        rw [hp] at hcover
        simpa only [ BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n) (BitVec.ofNat 64 136)] using hcover
set_option maxHeartbeats 600000 in
theorem call_agrees {variant : Variant} [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {offset : Nat} (h : CallSiteResult boundary ret s t)
    (hdst : rdi.read s = stackPtr s + BitVec.ofNat 64 variant.tailOffset + BitVec.ofNat 64 offset)
    (hlen : offset + (MemoryRoutines.rdx.read s).toNat ≤ 88) :
    AgreesExcept (variant.toKind.changes s) s t := by
  cases variant with
  | original =>
      apply h.agrees.widen
      · intro c hc hm
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Variant.tailOffset, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        · refine ⟨.mem (stackPtr s + BitVec.ofNat 64 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
          rw [hdst] at hcover
          exact FinalizeReset.Export.covers_shift hcover hlen
        · refine ⟨.mem (stackPtr s - 320) 320, by simp [Variant.toKind, Kind.changes], ?_⟩
          have hpush : pushAddr s = stackPtr s - 320 + BitVec.ofNat 64 312 := by
            simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
            rfl
          rw [hpush] at hcover
          exact FinalizeReset.Export.covers_shift hcover (by decide)
  | finalize =>
      apply h.agrees.widen
      · intro c hc hm
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Variant.tailOffset, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        · refine ⟨.mem (stackPtr s + BitVec.ofNat 64 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
          rw [hdst] at hcover
          exact FinalizeReset.Export.covers_shift hcover hlen
        · refine ⟨.mem (stackPtr s - 320) 320, by simp [Variant.toKind, Kind.changes], ?_⟩
          have hpush : pushAddr s = stackPtr s - 320 + BitVec.ofNat 64 312 := by
            simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
            rfl
          rw [hpush] at hcover
          exact FinalizeReset.Export.covers_shift hcover (by decide)
  | discard =>
      apply h.agrees.widen
      · intro c hc hm
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Variant.toKind, Variant.tailOffset, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        · refine ⟨.mem (stackPtr s + BitVec.ofNat 64 120) 168, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
          apply FinalizeReset.Export.covers_shift (offset := 16) (len := 88) _ (by decide)
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          change Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 136) 88) address
          rw [hdst] at hcover
          exact FinalizeReset.Export.covers_shift hcover hlen
        · refine ⟨.mem (stackPtr s - 320) 320, by simp [Variant.toKind, Kind.changes], ?_⟩
          have hpush : pushAddr s = stackPtr s - 320 + BitVec.ofNat 64 312 := by
            simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
            rfl
          rw [hpush] at hcover
          exact FinalizeReset.Export.covers_shift hcover (by decide)

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
