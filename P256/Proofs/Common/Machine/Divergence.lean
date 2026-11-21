import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Common.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

theorem advances_prefix [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel total : Nat} (run : Advances boundary total s t) (bound : fuel ≤ total) :
    ∃ u, Advances boundary fuel s u := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  change runSteps (Runner.step boundary) (fuel + extra) s = some (.outOfFuel t) at run
  rw [runSteps_add] at run
  cases front : runSteps (Runner.step boundary) fuel s with
  | none => simp [front] at run
  | some result =>
    cases result with
    | outOfFuel u => exact ⟨u, front⟩
    | returned u => simp [front] at run
    | ended success u => simp [front] at run
    | failed failure => simp [front] at run
    | reachedOSEntry entry u => simp [front] at run

theorem diverges_of_unbounded_advances [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (runs : ∀ fuel, ∃ total t, fuel ≤ total ∧ Advances boundary total s t) :
    Prelude.Diverges boundary s [] := by
  intro fuel
  obtain ⟨total, t, bound, run⟩ := runs fuel
  obtain ⟨u, front⟩ := advances_prefix run bound
  exact ⟨u, front, List.not_mem_nil⟩

theorem diverges_of_advances [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel : Nat} (run : Advances boundary fuel s t)
    (diverges : Prelude.Diverges boundary t []) : Prelude.Diverges boundary s [] := by
  apply diverges_of_unbounded_advances
  intro n
  obtain ⟨u, tail, _⟩ := diverges n
  exact ⟨fuel + n, u, by omega, run.trans tail⟩

theorem diverges_of_progress [Bindings] {boundary : ReturnBoundary} {invariant : RamState → Prop}
    (progress : ∀ s, invariant s →
      (∃ fuel t, 0 < fuel ∧ Advances boundary fuel s t ∧ invariant t) ∨
        Prelude.Diverges boundary s [])
    {initial : RamState} (start : invariant initial) : Prelude.Diverges boundary initial [] := by
  have bounded (budget : Nat) : ∀ s, invariant s → ∃ t, Advances boundary budget s t := by
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
      intro s hs
      by_cases zero : budget = 0
      · subst budget
        exact ⟨s, (advances_zero boundary s s).mpr rfl⟩
      · rcases progress s hs with ⟨steps, t, positive, run, ht⟩ | diverges
        · by_cases enough : budget ≤ steps
          · exact advances_prefix run enough
          · obtain ⟨u, tail⟩ := ih (budget - steps) (by omega) t ht
            exact ⟨u, by simpa only [Nat.add_sub_of_le (by omega : steps ≤ budget)]
              using run.trans tail⟩
        · obtain ⟨t, run, _⟩ := diverges budget
          exact ⟨t, run⟩
  intro fuel
  obtain ⟨t, run⟩ := bounded fuel initial start
  exact ⟨t, run, List.not_mem_nil⟩

end P256.Proofs.Common.Machine
