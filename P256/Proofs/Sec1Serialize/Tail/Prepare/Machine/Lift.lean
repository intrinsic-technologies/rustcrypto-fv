import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.Swap
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.Copy
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.StoreX
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.StoreY
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame

set_option autoImplicit false


namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem prepare_swap_stage
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312) (rip : t.RIP = 0x110fdc) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧ (prepareSwapEffect t).Holds t u := by
  have code : CodeIn (codeRange 0x110fdc prepareSwapBytes) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10fdc _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, u, run, ready, _, effect⟩ := prepare_swap boundary pre.outerBoundary
    t (readyToStep stage.machine stage.bindingsSupported) code (prepare_stack_frame pre stage (codeOffset := 0x10fdc)
      (by decide) rip)
  refine ⟨u, state_of_encoding pre stage ready effect ?_ ?_, ⟨fuel, run⟩, effect⟩
  · intro c hc
    simp only [prepareSwapEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [EncodingComponent]
    · simp [EncodingComponent]
    · exact ⟨88, rfl, by decide⟩
    · simp [EncodingComponent]
    · exact ⟨96, rfl, by decide⟩
    · simp [EncodingComponent]
    · exact ⟨104, rfl, by decide⟩
    · simp [EncodingComponent]
    · simp [EncodingComponent]
    · simp [EncodingComponent]
    · simp [EncodingComponent]
    · exact ⟨112, rfl, by decide⟩
    · simp [EncodingComponent]
    · trivial
  · simp [prepareSwapEffect, Effect.components, Write.component, Operand.component]

theorem prepare_copy_stage
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312) (rip : t.RIP = 0x111047) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧ (prepareCopyEffect t).Holds t u := by
  have code : CodeIn (codeRange 0x111047 prepareCopyBytes) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x11047 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, u, run, ready, _, effect⟩ := prepare_copy boundary pre.outerBoundary
    t (readyToStep stage.machine stage.bindingsSupported) code (prepare_stack_frame pre stage (codeOffset := 0x11047)
      (by decide) rip)
  refine ⟨u, state_of_encoding pre stage ready effect ?_ ?_, ⟨fuel, run⟩, effect⟩
  · intro c hc
    simp only [prepareCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨40, rfl, by decide⟩
    · exact ⟨32, rfl, by decide⟩
    · simp [EncodingComponent]
    · exact ⟨24, rfl, by decide⟩
    · exact ⟨16, rfl, by decide⟩
    · simp [EncodingComponent]
    · trivial
  · simp [prepareCopyEffect, Effect.components, Write.component, Operand.component]

theorem prepare_storex_stage
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312) (rip : t.RIP = 0x111071) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧ (prepareStoreXEffect t).Holds t u := by
  have code : CodeIn (codeRange 0x111071 prepareStoreXBytes) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x11071 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, u, run, ready, _, effect⟩ := prepare_storex boundary pre.outerBoundary
    t (readyToStep stage.machine stage.bindingsSupported) code (prepare_stack_frame pre stage (codeOffset := 0x11071)
      (by decide) rip)
  refine ⟨u, state_of_encoding pre stage ready effect ?_ ?_, ⟨fuel, run⟩, effect⟩
  · intro c hc
    simp only [prepareStoreXEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨200, rfl, by decide⟩
    · exact ⟨208, rfl, by decide⟩
    · exact ⟨216, rfl, by decide⟩
    · exact ⟨224, rfl, by decide⟩
    · trivial
  · simp [prepareStoreXEffect, Effect.components, Write.component, Operand.component]

theorem prepare_storey_stage
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312) (rip : t.RIP = 0x111098) :
    ∃ u, FrameState s u 65 328 312 ∧ (∃ fuel, Advances boundary fuel t u) ∧ (prepareStoreYEffect t).Holds t u := by
  have code : CodeIn (codeRange 0x111098 prepareStoreYBytes) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x11098 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, u, run, ready, _, effect⟩ := prepare_storey boundary pre.outerBoundary
    t (readyToStep stage.machine stage.bindingsSupported) code (prepare_stack_frame pre stage (codeOffset := 0x11098)
      (by decide) rip)
  refine ⟨u, state_of_encoding pre stage ready effect ?_ ?_, ⟨fuel, run⟩, effect⟩
  · intro c hc
    simp only [prepareStoreYEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.append_nil,
      List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [EncodingComponent]
    · exact ⟨232, rfl, by decide⟩
    · exact ⟨240, rfl, by decide⟩
    · exact ⟨248, rfl, by decide⟩
    · simp [EncodingComponent]
    · exact ⟨256, rfl, by decide⟩
    · trivial
  · simp [prepareStoreYEffect, Effect.components, Write.component, Operand.component]

end P256.Proofs.Sec1Serialize.Prepare
