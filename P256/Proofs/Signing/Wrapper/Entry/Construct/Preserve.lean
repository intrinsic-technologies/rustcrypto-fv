import P256.Proofs.Signing.Wrapper.Entry.Construct.Clear
import P256.Proofs.Signing.Wrapper.Entry.Construct.ClearCopy
import P256.Proofs.Signing.Wrapper.Entry.Construct.RepArguments
import P256.Proofs.Signing.Wrapper.Entry.Construct.FinalStore
import P256.Proofs.Signing.Wrapper.Entry.Construct.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar

theorem copy_preserves {s t : RamState} {src dst : BitVec 64} {d : Nat}
    (scalar : Nat256At s (stackPtr s+src) d)
    (ag : AgreesExcept (ScalarFrame.Copy32.components (stackPtr s+dst)) s t)
    (apart : OffsetsApart dst 32 src 32) : Nat256At t (stackPtr s+src) d := by
  refine ⟨scalar.1,fun i hi => ?_⟩
  apply Eq.trans (ag.byte ?_) (scalar.2 i hi)
  intro c hc cover
  simp only [ScalarFrame.Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> try exact cover.elim
  obtain ⟨j,hj,eq⟩ := cover
  exact apart.ne (stackPtr s) hj hi (by decide) eq.symm

theorem clear_bytes {s t : RamState}
    (effect : (Clear.effect s).Holds s t) {i : Nat} (hi : i<32) :
    t.external[stackPtr s+64+BitVec.ofNat 64 i]?=
      s.external[stackPtr s+64+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc cover
  simp only [Clear.effect,Effect.components,Write.component,Operand.component,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 176 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 184 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 192 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 200 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm

theorem clearcopy_bytes {s t : RamState}
    (effect : (ClearCopy.effect s).Holds s t) {i : Nat} (hi : i<32) :
    t.external[stackPtr s+64+BitVec.ofNat 64 i]?=
      s.external[stackPtr s+64+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc cover
  simp only [ClearCopy.effect,Effect.components,Write.component,Operand.component,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 0 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 8 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 16 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 24 8 64 32 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm

theorem reparguments_bytes {s t : RamState}
    (effect : (RepArguments.effect s).Holds s t) {i : Nat} (_hi : i<32) :
    t.external[stackPtr s+64+BitVec.ofNat 64 i]?=
      s.external[stackPtr s+64+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc cover
  simp only [RepArguments.effect,Effect.components,Write.component,Operand.component,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact cover.elim

theorem finalstore_bytes {s t : RamState}
    (effect : (FinalStore.effect s).Holds s t) {i : Nat} (hi : i<24) :
    t.external[stackPtr s+376+BitVec.ofNat 64 i]?=
      s.external[stackPtr s+376+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc cover
  simp only [FinalStore.effect,Effect.components,Write.component,Operand.component,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl
  all_goals try exact cover.elim
  · obtain ⟨j,hj,eq⟩ := cover
    exact (show OffsetsApart 368 8 376 24 by unfold OffsetsApart; decide +kernel).ne
      (stackPtr s) hj hi (by decide) eq.symm

end P256.Proofs.Signing.Wrapper.Entry.Construct
