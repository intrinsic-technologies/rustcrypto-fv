import Sha2.Proofs.Wrapper.Hash.Serialize.Machine
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper.Hash.Serialize.Memory
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Serialization
import Sha2.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Serialize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256

variable {v : Variant}

 theorem outputAddress_eq [Bindings] {initial s : RamState} (input : Preserved initial s v) :
    outputAddress s = initial.regValue .rcx := by
  unfold outputAddress
  rw [stack_address input.rsp]
  exact input.outputPointer

 theorem output_contains {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) {a : BitVec 64}
    (covered : (Component.mem (initial.regValue .rcx) v.outputBytes).Covers a) :
    (outputRegion v.routine initial).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  exact memoryRegion_contains_add call.outputInMemory.2.1 (Nat.le_refl _) (Nat.le_refl _) hi

 theorem output_readable [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : Wrapper.State initial s v) :
    MemReadable s (initial.regValue .rcx) v.outputBytes := by
  apply Common.Encoding.Serialize.readable_of_grow _ state.allocated
  exact memoryRegion_memReadable ctx.call.outputInMemory.2.1 ctx.call.outputInMemory.2.2
    (Nat.le_refl _) (Nat.le_refl _)

 theorem output_writable [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : Wrapper.State initial s v) :
    Common.Instructions.CrossPageStore.Writable s (initial.regValue .rcx) v.outputBytes := by
  have read := output_readable ctx state
  refine ⟨read, tables_of_not_reserved (by cases v <;> decide) read.low ?_⟩
  intro i hi reserved
  exact (ctx.call.separation.2 (outputRegion v.routine initial) (by simp)).2 _
    (output_contains ctx.call ⟨i, hi, rfl⟩) (.inr reserved)

 theorem output_codeApart [Bindings] {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) {offset len : Nat} (bound : offset + len ≤ 71757) :
    RangeApart (initial.regValue .rcx) v.outputBytes
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj eq
  apply (ctx.call.separation.2 (outputRegion v.routine initial) (by simp)).2 _
    (output_contains ctx.call ⟨i, hi, rfl⟩)
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

 theorem pre [Bindings] {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v) (input : Compressed initial s message v) : Pre s v := by
  refine ⟨input.rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [stack_address input.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_readable ctx input.toState (by decide) (by decide)
  · rw [stack_address input.rsp]
    exact stack_readable ctx input.toState (offset := 176) (by decide) (by decide)
  · intro i hi
    rw [outputAddress_eq input.toPreserved]
    cases v <;> simp only [Variant.outputBytes, Nat.reduceDiv, List.take_succ_cons,
      List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact (output_writable ctx input.toState).add _ (by decide)
    · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact (output_writable ctx input.toState).add _ (by decide)
  · intro i hi offset len bound
    rw [outputAddress_eq input.toPreserved]
    cases v <;> simp only [Variant.outputBytes, Nat.reduceDiv, List.take_succ_cons,
      List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Common.Instructions.RangeApart.add_left (h := output_codeApart ctx bound) _ (by decide)
    · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Common.Instructions.RangeApart.add_left (h := output_codeApart ctx bound) _ (by decide)

 def components (initial : RamState) (v : Variant := .sha256) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .mem (initial.regValue .rcx) v.outputBytes, .rip]

 theorem frame [Bindings] {initial s t : RamState} (input : Preserved initial s v)
    (h : (effect s v).Holds s t) : AgreesExcept (components initial v) s t := by
  have covers (offset : Nat) (bound : offset + 4 ≤ v.outputBytes) {a : BitVec 64}
      (ha : (Component.mem (outputAddress s + BitVec.ofNat 64 offset) 4).Covers a) :
      ∃ c ∈ components initial v, c.Covers a := by
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨.mem (initial.regValue .rcx) v.outputBytes, by simp [components],
      offset + i, by omega, ?_⟩
    rw [outputAddress_eq input, BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
  apply Common.Encoding.Serialize.agrees_of_footprint h.agrees
  · intro c hc hm
    cases v <;> simp only [effect, List.cons_append, List.nil_append, Effect.components,
      List.map_cons, List.map_nil, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [components, Component.isMem]
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [components, Component.isMem]
  · intro c hc a ha
    cases v <;> simp only [effect, List.cons_append, List.nil_append, Effect.components,
      List.map_cons, List.map_nil, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals first
        | exact covers 0 (by decide) ha
        | exact covers 4 (by decide) ha
        | exact covers 8 (by decide) ha
        | exact covers 12 (by decide) ha
        | exact covers 16 (by decide) ha
        | exact covers 20 (by decide) ha
        | exact covers 24 (by decide) ha
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals first
        | exact covers 0 (by decide) ha
        | exact covers 4 (by decide) ha
        | exact covers 8 (by decide) ha
        | exact covers 12 (by decide) ha
        | exact covers 16 (by decide) ha
        | exact covers 20 (by decide) ha
        | exact covers 24 (by decide) ha
        | exact covers 28 (by decide) ha

 theorem frame_stack [Bindings] {initial s t : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (h : AgreesExcept (components initial v) s t)
    {a : BitVec 64} (ha : (Stack.region initial v.routine.minStackBytes).Contains a.toNat) :
    t.external[a]? = s.external[a]? := by
  apply h.byte
  intro c hc covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  exact List.pairwise_pair.mp ctx.call.separation.1 a.toNat
    (output_contains ctx.call covered) ha

 theorem saved_contains {initial : RamState} {inputs : Array Input}
    (call : ValidCall v.routine initial inputs) {a : BitVec 64}
    (ha : (Component.mem (stackPtr initial - 48) 56).Covers a) :
    (Stack.region initial v.routine.minStackBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add call.stack.1 (len := 56) _ _ hi
  · change (Stack.region initial v.routine.minStackBytes).start ≤ (stackPtr initial - BitVec.ofNat 64 48).toNat
    rw [validCall_stack_sub_toNat call (offset := 48) (by decide)]
    change (stackPtr initial).toNat - 816 ≤ (stackPtr initial).toNat - 48
    omega
  · change (stackPtr initial - BitVec.ofNat 64 48).toNat + 56 ≤ _
    rw [stack_region_end, validCall_stack_sub_toNat call (offset := 48) (by decide)]
    have bounds := validCall_stack_bounds call
    omega

 theorem state [Bindings] {initial s t : RamState} {inputs : Array Input} {fuel : Nat}
    (ctx : Context initial inputs v) (input : Wrapper.State initial s v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (h : AgreesExcept (components initial v) s t) : Wrapper.State initial t v := by
  apply input.of_agrees ctx run ready h (hdf := by simp [components])
  · intro c hc a ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨outputRegion v.routine initial, by simp, output_contains ctx.call ha⟩
  · intro c hc a ha covered
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact List.pairwise_pair.mp ctx.call.separation.1 a.toNat
      (output_contains ctx.call covered)
      (saved_contains ctx.call ha)

 theorem preserved [Bindings] {initial s t : RamState} {inputs : Array Input} {fuel : Nat}
    (ctx : Context initial inputs v) (input : Preserved initial s v)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (h : AgreesExcept (components initial v) s t) : Preserved initial t v := by
  apply preserved_of_bytes input (state ctx input.toState run ready h)
    ((h.read (n := 64) (r := 4) (by simp [components])).trans input.rsp)
  intro a ha
  exact frame_stack ctx h
    (stackRegion_contains_sub ctx.call.stack.2.2.1
      (by change 176 ≤ 816; decide) (by decide) ha)

end Sha2.Proofs.Wrapper.Hash.Serialize
