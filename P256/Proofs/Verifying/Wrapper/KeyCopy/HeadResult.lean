import P256.Proofs.Verifying.Wrapper.KeyCopy.Head
import P256.Proofs.Verifying.Wrapper.KeyCopy.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (components s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map, List.cons_append, List.nil_append,
      Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals simp [components, Component.isMem] at *
  · intro a c hc covered
    simp only [effect, Effect.components, List.map, List.cons_append, List.nil_append,
      Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    · obtain ⟨i, hi, he⟩ := covered
      refine ⟨.mem (stackPtr s) 65, by simp [components], 2+i, by omega, ?_⟩
      simpa [BitVec.ofNat_add, BitVec.add_assoc, stackPtr, Operand.read_reg64, gprIndex] using he
    · obtain ⟨i, hi, he⟩ := covered
      exact ⟨.mem (stackPtr s) 65, by simp [components], i, by omega, he⟩

theorem copied {s t : RamState} (pre : Pre 0x103088 s) (h : (effect s).Holds s t) :
    ∀ i < 3, t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 i]? := by
  have values : memLoad t.external (stackPtr s+2) 8 = memLoad s.external (s.regValue .rdx+2) 8 ∧
      memLoad t.external (stackPtr s) 16 = memLoad s.external (s.regValue .rdx) 16 ∧
      t.regValue .rax = (memLoad s.external (s.regValue .rdx+3) 32).setWidth 64 := h.writes
  have first := chunk_bytes pre h.agrees.grow 0 16 (by decide) (by simpa using values.2.1)
  have third := chunk_bytes pre h.agrees.grow 2 8 (by decide) values.1
  intro i hi
  by_cases small : i < 2
  · simpa using first i small
  · have eq : i=2 := by omega
    subst i
    exact third 0 (by decide)

end P256.Proofs.Verifying.Wrapper.KeyCopy.Head
