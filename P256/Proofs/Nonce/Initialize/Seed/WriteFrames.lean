import P256.Proofs.Nonce.Initialize.Seed.Initialize
import P256.Proofs.Nonce.Initialize.Seed.Descriptors
import P256.Proofs.Nonce.Initialize.Seed.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_writes (s : RamState) :
    ∀ c ∈ (initializeEffect s).components, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + 8) 64).Covers a := by
  intro c hc a ha
  simp only [initializeEffect, Effect.components, List.map_cons, List.map_nil, List.nil_append,
    List.append_nil, List.cons_append, Write.component_mem, Write.component_reg,
    List.mem_cons, List.not_mem_nil, or_false, Operand.read_reg64] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals exact component_subrange (start := 8) (count := 64) (by decide) (by decide) ha

theorem descriptors_writes (s : RamState) :
    ∀ c ∈ (descriptorsEffect s).components, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + 104) 48).Covers a := by
  intro c hc a ha
  simp only [descriptorsEffect, Effect.components, List.map_cons, List.map_nil, List.nil_append,
    List.append_nil, List.cons_append, Write.component_mem, Write.component_reg,
    List.mem_cons, List.not_mem_nil, or_false, Operand.read_reg64] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals exact component_subrange (start := 104) (count := 48) (by decide) (by decide) ha

end P256.Proofs.Nonce.Initialize.Seed
