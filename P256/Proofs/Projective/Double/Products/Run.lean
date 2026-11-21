import P256.Proofs.Projective.Double.Products.Subtract
import P256.Proofs.Projective.Double.Products.Add
import P256.Proofs.Projective.Double.Products.YProduct
import P256.Proofs.Projective.Double.Products.XProduct
import P256.Proofs.Projective.Double.Products.Memory
set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

namespace Products

theorem subtraction_local {t : RamState} :
    ∀ c ∈ (subtractionEffect t).components, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i := by
  intro c hc a ha
  simp only [subtractionEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨32+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨40+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨48+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨56+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨64+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩

theorem subtraction_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x105fd1) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧ (subtractionEffect t).Holds t u ∧
      MemoryWriteFrame t u #v[workRegion s 1016] ∧
      (∀ offset x, offset ≤ 656 → 32 ≤ offset →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x) := by
  apply move_run pre state (subtraction_setup boundary pre.outerBoundary) (pc := 0x5fd1)
    (by decide +kernel) (by decide +kernel) rip
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    subtraction_local (by simp [subtractionEffect, Effect.components])

theorem addition_local {t : RamState} :
    ∀ c ∈ (additionEffect t).components, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i := by
  intro c hc a ha
  simp only [additionEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨32+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩

theorem addition_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x106053) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧ (additionEffect t).Holds t u ∧
      MemoryWriteFrame t u #v[workRegion s 1016] ∧
      (∀ offset x, offset ≤ 656 → 32 ≤ offset →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x) := by
  apply move_run pre state (addition_setup boundary pre.outerBoundary) (pc := 0x6053)
    (by decide +kernel) (by decide +kernel) rip
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    addition_local (by simp [additionEffect, Effect.components])

theorem y_product_local {t : RamState} :
    ∀ c ∈ (y_productEffect t).components, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i := by
  intro c hc a ha
  simp only [y_productEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨32+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩

theorem y_product_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x10609f) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧ (y_productEffect t).Holds t u ∧
      MemoryWriteFrame t u #v[workRegion s 1016] ∧
      (∀ offset x, offset ≤ 656 → 32 ≤ offset →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x) := by
  apply move_run pre state (y_product_setup boundary pre.outerBoundary) (pc := 0x609f)
    (by decide +kernel) (by decide +kernel) rip
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl | rfl | rfl <;> decide)
    y_product_local (by simp [y_productEffect, Effect.components])

theorem x_product_local {t : RamState} :
    ∀ c ∈ (x_productEffect t).components, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i := by
  intro c hc a ha
  simp only [x_productEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim

theorem x_product_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x1060eb) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧ (x_productEffect t).Holds t u ∧
      MemoryWriteFrame t u #v[workRegion s 1016] ∧
      (∀ offset x, offset ≤ 656 → 32 ≤ offset →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x) := by
  apply move_run pre state (x_product_setup boundary pre.outerBoundary) (pc := 0x60eb)
    (by decide +kernel) (by decide +kernel) rip
    (by intro i hi; exact False.elim (List.not_mem_nil hi))
    (by intro i hi; exact False.elim (List.not_mem_nil hi))
    x_product_local (by simp [x_productEffect, Effect.components])

theorem subtraction_copy_8 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (effect : (subtractionEffect t).Holds t u)
    (input : MontgomeryAt t (stackPtr s - 432) x) :
    MontgomeryAt u (stackPtr s - 720) x := by
  apply copy_words pre state effect.agrees (src := 296) (dst := 8) (by decide) (by decide) input
  intro j hj
  rcases effect.writes with ⟨_, _, _, _, _, _, h0, h1, h2, h3, _, _, _, _⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem subtraction_copy_40 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (effect : (subtractionEffect t).Holds t u)
    (input : MontgomeryAt t (stackPtr s - 592) x) :
    MontgomeryAt u (stackPtr s - 688) x := by
  apply copy_words pre state effect.agrees (src := 136) (dst := 40) (by decide) (by decide) input
  intro j hj
  rcases effect.writes with ⟨_, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem addition_copy_8 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (effect : (additionEffect t).Holds t u)
    (input : MontgomeryAt t (stackPtr s - 592) x) :
    MontgomeryAt u (stackPtr s - 720) x := by
  apply copy_words pre state effect.agrees (src := 136) (dst := 8) (by decide) (by decide) input
  intro j hj
  rcases effect.writes with ⟨_, _, _, _, _, _, h0, h1, h2, h3⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem y_product_copy_8 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (effect : (y_productEffect t).Holds t u)
    (input : MontgomeryAt t (stackPtr s - 400) x) :
    MontgomeryAt u (stackPtr s - 720) x := by
  apply copy_words pre state effect.agrees (src := 328) (dst := 8) (by decide) (by decide) input
  intro j hj
  rcases effect.writes with ⟨_, _, _, _, _, _, h0, h1, h2, h3⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3


end Products
end P256.Proofs.Projective.Double
