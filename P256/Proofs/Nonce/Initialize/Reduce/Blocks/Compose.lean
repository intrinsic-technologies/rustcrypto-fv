import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Copy
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Low
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Second
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Third
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.High
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Store
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.ChoiceMiddle
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.ChoiceHigh
import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Arguments

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce.Blocks

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem copy_local : Effect.Local copyEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [copyEffect, stackPtr, h.read_mem, h.gpr]
  · intro s
    simp [copyEffect, Write.Full, Operand.Full]

theorem copy_writes (s : RamState) : ∀ c ∈ (copyEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem low_local : Effect.Local lowEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowEffect, stackPtr, h.read_reg, h.gpr]
  · intro s
    simp [lowEffect, Write.Full, Operand.Full]

theorem low_writes (s : RamState) : ∀ c ∈ (lowEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [lowEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem second_local : Effect.Local secondEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [secondEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [secondEffect, Write.Full, Operand.Full]

theorem second_writes (s : RamState) : ∀ c ∈ (secondEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [secondEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem third_local : Effect.Local thirdEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [thirdEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [thirdEffect, Write.Full, Operand.Full]

theorem third_writes (s : RamState) : ∀ c ∈ (thirdEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [thirdEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem high_local : Effect.Local highEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [highEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [highEffect, Write.Full, Operand.Full]

theorem high_writes (s : RamState) : ∀ c ∈ (highEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [highEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem store_local : Effect.Local storeEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

theorem store_writes (s : RamState) : ∀ c ∈ (storeEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [storeEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem choiceMiddle_local : Effect.Local choiceMiddleEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [choiceMiddleEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [choiceMiddleEffect, Write.Full, Operand.Full]

theorem choiceMiddle_writes (s : RamState) : ∀ c ∈ (choiceMiddleEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [choiceMiddleEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem choiceHigh_local : Effect.Local choiceHighEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [choiceHighEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [choiceHighEffect, Write.Full, Operand.Full]

theorem choiceHigh_writes (s : RamState) : ∀ c ∈ (choiceHighEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [choiceHighEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

theorem arguments_local : Effect.Local argumentsEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [argumentsEffect, stackPtr, h.read_reg, h.read_mem, h.gpr]
  · intro s
    simp [argumentsEffect, Write.Full, Operand.Full]

theorem arguments_writes (s : RamState) : ∀ c ∈ (argumentsEffect s).components, ∀ a,
    c.Covers a → (Component.mem (stackPtr s) 232).Covers a := by
  intro c hc a ha
  simp only [argumentsEffect, Effect.components, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Write.component_reg,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact local_covers (by decide) ha

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
