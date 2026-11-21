import Sha1.Spec.Program

namespace Sha1.Proofs.Common.Call

open Sha1.Spec.Program Prelude X86

theorem separation_pair {input output stack : MemoryRegion}
    (h : Sha1.Spec.Program.MemorySeparation [input] output stack) :
    MemoryRegion.PairwiseDisjoint #v[input, output, stack] ∧
      ∀ region ∈ #v[output, stack],
        region.Avoids fun address => InProgram address ∨ InPageTables address := by
  refine ⟨?_, fun region hr ↦ (h.2 region hr).2⟩
  have ho := (h.2 output (by simp)).1 input (by simp)
  have hs := (h.2 stack (by simp)).1 input (by simp)
  have hw := h.1
  intro i j hij
  have cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ho
  · exact hs
  · exact hw

end Sha1.Proofs.Common.Call
